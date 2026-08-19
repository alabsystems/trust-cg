// crates/rustc-codegen-trust-cg/src/mem_refine.rs
//
// Phase P1 (FIRST RULE) — per-compile MEMORY refinement of the fixed-offset
// nested-projection SCALAR FIELD LOAD lowering (`dst = o.b.x`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY AN EMITTED-OP FOLD (the anti-tautology requirement)
// -------------------------------------------------------
// `trust_cg_verify::mir_semantics::check_memory_sequence` validates that the
// BRIDGE's lowered load/store sequence preserves the SOURCE program's memory
// semantics: it symbolically executes BOTH a SPEC `MirMemOp` sequence and a
// BRIDGE `MirMemOp` sequence against the SAME fresh symbolic `Array(BV64,BV8)`
// memory and asks the solver whether any load can observe a different value (or
// any final-memory cell differ). A wrong byte offset, a swapped base, a wrong
// width, or a dropped store yields a genuinely different `MirMemOp` sequence and
// is REFUTED.
//
// The naive wiring — building the BRIDGE side from the same layout walk the
// SPEC uses — would be a TAUTOLOGY (`offset == offset`). This module breaks the
// tautology with an INDEPENDENT derivation of the bridge side: a small symbolic
// fold over the trust-ir instructions the bridge ACTUALLY EMITTED for the
// lowered statement (the `Const`/`Copy`/`PtrToInt`/`Mul`/`Add`/`IntToPtr`
// address arithmetic of `emit_element_addr`, then the `Load`/`Store`). The
// SPEC side (`crate::spec_field_load_mem_ops`) resolves the place's
// Field/Downcast chain to a byte offset + leaf size INDEPENDENTLY via rustc's
// `layout_of(...).fields.offset(i)`. The two derivations meet only on the
// shared symbolic base name (`mem_base_name`), so a bridge that EMITS the load
// at the wrong offset / through a different base / at the wrong width yields a
// `MirMemOp` that genuinely differs from the layout-designated spec -> Refuted.
//
// READING THE REAL EMITTED OPS is the keystone: the fold reconstructs the
// offset from the emitted `Const`/`Mul`/`Add` (NOT from a fresh layout query)
// and the width from the emitted `Load`'s `ty`. See the unit tests at the
// bottom — they fold a CORRECT emitted sequence (not Refuted) and a WRONG one
// (Refuted) over the same fixture.
//
// SCOPE (the honest slice): a FIXED-offset address expression of the exact shape
// the bridge emits for a slot field access — `base (+ const_offset)` reached
// through `Copy`/`PtrToInt`/`IntToPtr` reinterpretations and `Add`/`Mul` over
// integer constants — terminated by a single scalar typed `Load` (or `Store`).
// ANY other instruction in the captured slice (a runtime index `Mul` by a
// non-constant, a second pointer base, an aggregate op, a call, ...) bails the
// fold to `None`: the statement is SKIPPED, never guessed at (sound: less
// coverage, never a wrong verdict).

use std::collections::HashMap;

use trust_cg_verify::mir_semantics::{
    range_next_spec, range_next_spec_w, slice_first_last_spec, slice_iter_next_spec, split_at_spec,
    split_first_last_spec, step_by_next_packed_spec, step_by_next_slice_spec, step_by_next_spec,
    stride_iter_ctor_spec, vec_index_spec, vec_range_subslice_spec, MemAddr, MirMemOp,
    OptionRefSpec, RangeForm, RangeNextSpec, SliceEndKind, SliceIterNextSpec, SplitAtSpec,
    SplitEndsSpec, StepByNextPackedSpec, StepByNextSliceSpec, StepByNextSpec, StrideIterCtorSpec,
    VecIndexSpec, VecRangeSubsliceSpec,
};
use trust_cg_verify::{MachineSideProvenance, ProofObligation, SmtExpr, TransvalCheckKind};
use trust_ir::{
    BinOp as TrustIrBinOp, CastOp, Constant, ICmpOp, Inst, InstrNode, Ty as TrustIrTy, ValueId,
};

/// The thin-pointer width, in bits, of the 64-bit targets the bridge emits for
/// (`emit_element_addr` does its address arithmetic at `I64`). Used to size
/// pointer-like scalar leaves.
const PTR_BITS: u32 = 64;

/// Canonical symbolic 64-bit base-pointer name for a slot/base `ValueId`.
///
/// SHARED by the SPEC encoder (`crate::spec_field_load_mem_ops`) and the IMPL
/// fold below, so a CORRECT lowering anchors both sides of the memory VC on the
/// SAME symbolic base (and the VC reduces to an offset/width comparison), while
/// a SWAPPED base — the emitted load reached through a DIFFERENT `ValueId` —
/// yields a DIFFERENT name, a distinct symbolic base, and a REFUTED VC.
pub(crate) fn mem_base_name(v: ValueId) -> String {
    format!("mem_base_v{}", v.index())
}

/// Canonical symbolic name for the value an emitted `Store` of `width` bytes
/// writes. Shared with the spec side so a store-disjointness VC is driven by the
/// SAME free var on both sides (the store carries the lowered value, by
/// construction). The WIDTH is part of the name so a CORRECT store (spec width ==
/// emitted width) anchors both sides on the same var (and the final-memory VC
/// reduces to an offset comparison), while a WRONG-WIDTH store yields a DIFFERENT
/// name — a cleanly distinct var (no same-name/two-widths encoding hazard) that
/// the byte-range VC refutes.
pub(crate) fn mem_store_value_name(v: ValueId, width: u32) -> String {
    format!("mem_stval_v{}_w{}", v.index(), width)
}

/// Canonical symbolic name for "the original contents of the `width`-agnostic
/// source cell `src_base + off`" — the value a multi-lane aggregate copy reads
/// from the source and must write to the destination. SHARED between the SPEC
/// (layout-derived lane offsets) and the IMPL fold (offsets reconstructed from
/// the EMITTED load address), so a CORRECT copy anchors the dst-cell value on the
/// SAME free var as the layout spec, while a copy that loads the WRONG source
/// cell / through the WRONG base names a DIFFERENT var and the final-memory VC
/// refutes. This is the keystone that captures the load->store DATAFLOW by
/// NAMING: the value stored at `dst+off` is identified by the source cell it was
/// loaded from, so a mis-sourced lane is a genuinely different `MirMemOp`.
pub(crate) fn mem_lane_name(src_base: ValueId, off: u64) -> String {
    format!("mem_lane_v{}_off{}", src_base.index(), off)
}

/// Byte width of a SCALAR trust-ir leaf type on the bridge's 64-bit target, or
/// `None` for a non-scalar (vector / aggregate / unit / never) type — which is
/// out of the single-typed-access memory slice.
pub(crate) fn scalar_byte_width(ty: &TrustIrTy) -> Option<u32> {
    if ty.is_vector() {
        return None;
    }
    let bits = ty.bit_width_with(PTR_BITS)?;
    if bits == 0 {
        return None;
    }
    Some(bits.div_ceil(8))
}

/// Build the SHARED memory-conditioning harness + the SPEC load sequence for a
/// fixed-offset field LOAD of `width` bytes at `base + offset`.
///
/// WHY A HARNESS STORE. The verifier models a fresh memory as a UNIFORM
/// `ConstArray` whose every unwritten cell reads the SAME symbolic default byte
/// (so a load of a never-written cell is identical on both sides and is not
/// spuriously refuted). A bare load-vs-load VC is therefore VACUOUS for an
/// offset difference: every cell reads the same default, so a wrong offset would
/// observe the SAME value as the right one. To make the load address OBSERVABLE
/// we condition the memory with a store of a FRESH symbolic field value at the
/// layout-designated cell, added IDENTICALLY to BOTH sequences (it is NOT
/// claimed to be an emitted bridge op — it establishes the precondition "the
/// object's field holds `field_val`"). The spec then LOADS that cell (observes
/// `field_val`); the bridge's EMITTED load must observe the SAME `field_val`,
/// i.e. read the SAME cell — a WRONG offset reads a different (defaulted /
/// neighbouring) cell, so the value VC REFUTES. This is the same conditioning
/// the `mem_*_refuted_with_probe` tests use, and it keeps the obligation
/// NON-DEGENERATE: the spec offset is layout-derived while the bridge offset is
/// reconstructed independently from the emitted ops.
///
/// Returns `(harness, spec_ops)`: `harness` is the shared prefix to prepend to
/// the FOLDED bridge ops, and `spec_ops == harness ++ [spec load]`.
pub(crate) fn field_load_obligation(
    base_name: String,
    offset: u64,
    width: u32,
) -> (Vec<MirMemOp>, Vec<MirMemOp>) {
    let harness = vec![MirMemOp::Store {
        addr: MemAddr {
            base: base_name.clone(),
            offset,
        },
        value: SmtExpr::var("p1_field_load_val".to_string(), width * 8),
        width,
    }];
    let mut spec_ops = harness.clone();
    spec_ops.push(MirMemOp::Load {
        addr: MemAddr {
            base: base_name,
            offset,
        },
        width,
        dst: "spec_load0".to_string(),
    });
    (harness, spec_ops)
}

/// Build the SHARED memory-conditioning harness + the SPEC store sequence for a
/// fixed-offset field STORE of the lowered value `stored_value` (`width` bytes)
/// into `base + offset`, leaving every `siblings` cell `(off, w)` UNCHANGED.
///
/// SPEC (the meaning of `o.b.x = v`):
///   * after the store, `bytes(base, offset .. offset+width) == v`, AND
///   * `bytes(base, elsewhere) == old` (DISJOINTNESS / sibling isolation): the
///     write touches exactly the layout-designated field, nothing else.
///
/// HOW THE OBLIGATION ENCODES THAT. The `harness` PINS a fresh distinct OLD
/// symbolic value into each `siblings` cell (the real layout-neighbour leaves,
/// e.g. `o.b.y`, `o.a`), establishing the precondition "the object's other
/// fields hold old values". It is prepended IDENTICALLY to both the spec and the
/// folded bridge sequences. The SPEC then stores the NEW value `v` at exactly the
/// target cell and TOUCHES NOTHING ELSE — so its final memory holds `v` at the
/// field and `old` at every sibling. `check_memory_sequence`'s final-memory
/// equality is taken over the UNION of EVERY cell EITHER side stores to, so:
///   * a bridge store at the WRONG offset leaves the target at `old` (spec has
///     `v`) AND writes a cell the spec left at `old` -> REFUTED;
///   * a bridge store of the WRONG width spans a different byte range than the
///     spec's `v` (a distinct value var) -> REFUTED;
///   * a bridge that CLOBBERS a sibling overwrites a pinned `old` cell the spec
///     preserves -> REFUTED (the disjointness / sibling-unchanged property);
///   * a bridge that stores the WRONG value names a different var than the
///     shared `v` -> REFUTED.
/// Every address is the SAME symbolic base at a distinct CONSTANT offset, so all
/// pairs are provably `Distinct`/`Equal` (never `Unknown`) and no disjointness
/// precondition is required — `MemCheckConfig::default()` discharges it.
///
/// Returns `(harness, spec_ops)`: `harness` is the shared sibling-pinning prefix
/// to prepend to the FOLDED bridge store, and `spec_ops == harness ++ [spec
/// store of v at the target]`.
pub(crate) fn field_store_obligation(
    base_name: String,
    offset: u64,
    width: u32,
    stored_value: ValueId,
    siblings: &[(u64, u32)],
) -> (Vec<MirMemOp>, Vec<MirMemOp>) {
    // Pin a fresh OLD value into each sibling cell. The target cell is left
    // unpinned: both sides write it (spec with `v`, a correct bridge with `v`),
    // and a wrong-offset bridge that fails to write it is caught because the
    // spec's `v` there meets the bridge's untouched default.
    let mut harness: Vec<MirMemOp> = Vec::with_capacity(siblings.len());
    for (i, (soff, swidth)) in siblings.iter().enumerate() {
        harness.push(MirMemOp::Store {
            addr: MemAddr {
                base: base_name.clone(),
                offset: *soff,
            },
            value: SmtExpr::var(format!("p1_field_store_old_sib{i}"), swidth * 8),
            width: *swidth,
        });
    }
    let mut spec_ops = harness.clone();
    spec_ops.push(MirMemOp::Store {
        addr: MemAddr {
            base: base_name,
            offset,
        },
        value: SmtExpr::var(mem_store_value_name(stored_value, width), width * 8),
        width,
    });
    (harness, spec_ops)
}

/// Build the SPEC store sequence for a multi-lane whole-aggregate COPY
/// `dst = src` (the lane-by-lane `load src+off; store dst+off` the bridge emits
/// for two same-layout memory slots): for each lane `0..lanes`, store into
/// `dst_base + lane*width` the value named for the SOURCE cell `src_base +
/// lane*width` (`mem_lane_name`). Each lane is `width` bytes (the slot's natural
/// integer lane), so the whole `width*lanes`-byte aggregate is copied.
///
/// The IMPL side (`fold_emitted_copy_ops`) reconstructs the SAME per-lane stores
/// from the EMITTED load/store addresses (naming each stored value by the source
/// cell its load read), so a DROPPED lane, a WRONG lane offset, or a SWAPPED
/// src/dst yields a different `MirMemOp` sequence and the final-memory VC refutes.
pub(crate) fn aggregate_copy_spec(
    src_base: ValueId,
    dst_base: ValueId,
    width: u32,
    lanes: u64,
) -> Vec<MirMemOp> {
    let mut ops = Vec::with_capacity(lanes as usize);
    for lane in 0..lanes {
        let offset = lane * u64::from(width);
        ops.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(dst_base),
                offset,
            },
            value: SmtExpr::var(mem_lane_name(src_base, offset), width * 8),
            width,
        });
    }
    ops
}

/// A folded value in the address-arithmetic lattice the bridge emits for a
/// fixed-offset place access (`emit_element_addr` + `emit_typed_load/store`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum AddrVal {
    /// A known integer constant (a byte offset, an element index, or a stride).
    Int(i128),
    /// `base + off` bytes — a pointer, or its `PtrToInt` integer image (the two
    /// denote the SAME address, so they share this representation). `base` is a
    /// `ValueId` the captured slice never defines (the slot/base pointer, an
    /// earlier `Alloca`/argument); `off` is the accumulated CONSTANT byte offset
    /// reconstructed purely from the emitted `Const`/`Mul`/`Add` chain.
    Ptr { base: ValueId, off: i128 },
}

/// Resolve an operand through the fold environment.
///
/// A `ValueId` the captured slice never DEFINES is, by construction, the BASE
/// pointer the address arithmetic starts from (the slot address comes from an
/// earlier `Alloca`/argument outside the per-statement slice). Name it
/// symbolically at offset 0 — this is the "faithful naming of undefined values"
/// pattern (cf. `trust_ir_interp`'s preheader-arg `base` closure). A constant
/// or a value produced WITHIN the slice was already bound by its defining
/// instruction, so it never falls through to here.
fn lookup(env: &HashMap<ValueId, AddrVal>, v: ValueId) -> AddrVal {
    env.get(&v)
        .cloned()
        .unwrap_or(AddrVal::Ptr { base: v, off: 0 })
}

/// Bind the single result of `node` to `val`. `None` if the instruction does not
/// have exactly one result (out of slice).
fn bind(env: &mut HashMap<ValueId, AddrVal>, node: &InstrNode, val: AddrVal) -> Option<()> {
    let [result] = node.results.as_slice() else {
        return None;
    };
    env.insert(*result, val);
    Some(())
}

/// Fold the EMITTED trust-ir instructions of ONE lowered statement into the
/// `MirMemOp` sequence the bridge actually performs.
///
/// `nodes` is the exact, ordered slice of instructions the bridge appended to
/// the block while lowering the statement (captured by the caller as
/// `block.body[start..]`). The fold reconstructs each address as `base + off`
/// from the real `Const`/`Mul`/`Add`/`PtrToInt`/`IntToPtr` chain, and each
/// access's width from the real `Load`/`Store` `ty`. Returns `None` (skip the
/// statement, sound) for ANY instruction outside the fixed-offset scalar slice.
///
/// Crucially this never consults the layout — so a wrong EMITTED offset/width
/// produces a wrong `MirMemOp` here, and the memory VC against the
/// layout-derived spec REFUTES (the anti-tautology guarantee).
pub(crate) fn fold_emitted_mem_ops(nodes: &[InstrNode]) -> Option<Vec<MirMemOp>> {
    let mut env: HashMap<ValueId, AddrVal> = HashMap::new();
    let mut ops: Vec<MirMemOp> = Vec::new();
    let mut load_ctr = 0usize;

    for node in nodes {
        // Address-arithmetic (`Const`/`Copy`/`PtrToInt`/`IntToPtr`/`Add`/`Mul`)
        // is folded into `env` by the shared step; `Load`/`Store` (and anything
        // out of slice) fall through.
        match fold_addr_step(&mut env, node)? {
            true => continue,
            false => {}
        }
        match &node.inst {
            // The scalar typed load: reconstruct `MemAddr{base, off}` + width.
            Inst::Load { ty, ptr, .. } => {
                let AddrVal::Ptr { base, off } = lookup(&env, *ptr) else {
                    return None;
                };
                let width = scalar_byte_width(ty)?;
                let offset = u64::try_from(off).ok()?;
                ops.push(MirMemOp::Load {
                    addr: MemAddr {
                        base: mem_base_name(base),
                        offset,
                    },
                    width,
                    dst: format!("impl_load{load_ctr}"),
                });
                load_ctr += 1;
                // The loaded value is a fresh scalar (not an address); do NOT
                // bind it — a later use of it as a base would then be named as a
                // distinct external base (and refuted), never silently folded.
            }

            // The scalar typed store: reconstruct `MemAddr{base, off}` + width;
            // the stored value is the lowered SSA value, named (with its width)
            // so the SAME var can be driven on the spec side (a real
            // store-disjointness VC).
            Inst::Store {
                ty, ptr, value, ..
            } => {
                let AddrVal::Ptr { base, off } = lookup(&env, *ptr) else {
                    return None;
                };
                let width = scalar_byte_width(ty)?;
                let offset = u64::try_from(off).ok()?;
                ops.push(MirMemOp::Store {
                    addr: MemAddr {
                        base: mem_base_name(base),
                        offset,
                    },
                    value: SmtExpr::var(mem_store_value_name(*value, width), width * 8),
                    width,
                });
            }

            // Anything else in the slice (a second-base GEP, an aggregate op, a
            // call, a non-Int const, a non-Add/Mul binop, ...) is out of the
            // fixed-offset scalar memory model: skip the statement (sound).
            _ => return None,
        }
    }
    Some(ops)
}

/// Fold ONE address-arithmetic instruction into `env`. The fold's keystone (it
/// reconstructs `base + const_offset` from the REAL emitted `Const`/`Copy`/
/// `PtrToInt`/`IntToPtr`/`Add`/`Mul` chain, never a layout query). Returns:
///   * `Some(true)`  — handled (an address-arith node, bound into `env`);
///   * `Some(false)` — NOT an address-arith node (caller handles `Load`/`Store`
///                     or treats it as out of slice);
///   * `None`        — an address-arith node that is OUT OF SLICE (a runtime-index
///                     `Mul`, an `IntToPtr` of a non-address int, a `base+base`,
///                     an overflowing offset, a multi-result node): BAIL the fold.
fn fold_addr_step(env: &mut HashMap<ValueId, AddrVal>, node: &InstrNode) -> Option<bool> {
    match &node.inst {
        // An integer address constant (an offset, an index, the stride).
        Inst::Const {
            value: Constant::Int(v),
            ..
        } => {
            bind(env, node, AddrVal::Int(*v))?;
            Some(true)
        }

        // A pointer/int reinterpreting move (`coerce_to_plain_ptr` /
        // `coerce_to_i64` both emit a `Copy`): propagate the operand value.
        Inst::Copy { operand, .. } => {
            let val = lookup(env, *operand);
            bind(env, node, val)?;
            Some(true)
        }

        // `PtrToInt` / `IntToPtr`: the integer image of a pointer (and back)
        // denotes the SAME address. Only a pointer value may flow here; an
        // `IntToPtr` of a non-address integer is out of slice. WIDTH GATE (the
        // lane-9 width class): a NARROW cast TRUNCATES the address at machine
        // level while the fold would keep the full `base + off` — only 8-byte
        // casts are in slice.
        Inst::Cast {
            op: CastOp::PtrToInt | CastOp::IntToPtr,
            src_ty,
            dst_ty,
            operand,
        } => {
            if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                return None;
            }
            match lookup(env, *operand) {
                p @ AddrVal::Ptr { .. } => {
                    bind(env, node, p)?;
                    Some(true)
                }
                AddrVal::Int(_) => None,
            }
        }

        // `base + const_offset` (or `const + const`).
        Inst::BinOp {
            op: TrustIrBinOp::Add,
            lhs,
            rhs,
            ..
        } => {
            let combined = match (lookup(env, *lhs), lookup(env, *rhs)) {
                (AddrVal::Ptr { base, off }, AddrVal::Int(k))
                | (AddrVal::Int(k), AddrVal::Ptr { base, off }) => AddrVal::Ptr {
                    base,
                    off: off.checked_add(k)?,
                },
                (AddrVal::Int(a), AddrVal::Int(b)) => AddrVal::Int(a.checked_add(b)?),
                // base + base: not an address expression this slice models.
                (AddrVal::Ptr { .. }, AddrVal::Ptr { .. }) => return None,
            };
            bind(env, node, combined)?;
            Some(true)
        }

        // `index * stride` — BOTH operands must be constants (a fixed offset). A
        // runtime-index `Mul` (one operand a base/non-constant) is out of the
        // fixed-offset slice.
        Inst::BinOp {
            op: TrustIrBinOp::Mul,
            lhs,
            rhs,
            ..
        } => match (lookup(env, *lhs), lookup(env, *rhs)) {
            (AddrVal::Int(a), AddrVal::Int(b)) => {
                bind(env, node, AddrVal::Int(a.checked_mul(b)?))?;
                Some(true)
            }
            _ => None,
        },

        // Not an address-arith instruction (a `Load`/`Store`, or out of slice).
        _ => Some(false),
    }
}

/// Fold the EMITTED trust-ir of a multi-lane whole-aggregate COPY `dst = src`
/// (the lane-by-lane `load src+off; store dst+off` loop) into the per-lane
/// destination `Store` sequence the bridge actually performs.
///
/// STORES-ONLY MODEL. A copy's loads are pure reads (no memory effect); the only
/// memory effect is the destination stores, and the only correctness question is
/// "does dst-cell `c` end up holding the ORIGINAL contents of the right src
/// cell?". So this fold drops the loads from the `MirMemOp` sequence and instead
/// captures the load->store DATAFLOW BY NAMING: a `Load` from `src_base+off`
/// binds its result to the canonical source-cell name (`mem_lane_name`), and a
/// `Store` whose value operand is THAT loaded value emits `Store{dst+off ←
/// mem_lane_name(src_base, src_off)}`. The SPEC (`aggregate_copy_spec`) builds
/// the same per-lane stores from the LAYOUT, so:
///   * a DROPPED lane omits a dst-cell store the spec keeps -> the spec's value
///     meets the bridge's untouched default at that cell -> REFUTED (no
///     load-count dependence: a dropped load+store does NOT become a structural
///     skip, it becomes a final-memory refutation);
///   * a WRONG lane offset names the wrong source cell / writes the wrong dst
///     cell -> a different var / a spurious write -> REFUTED;
///   * a SWAPPED src/dst loads from dst and stores to src -> mis-targeted stores
///     and mis-sourced values -> REFUTED.
///
/// Returns `None` (skip, sound) for ANYTHING that is not this exact shape: a
/// store whose value is NOT a value loaded earlier in the slice (not a pure
/// copy), a load/store width mismatch within a lane, a src/dst that ALIAS the
/// same base (an in-place overlap the initial-contents naming would mismodel),
/// or any instruction outside the fixed-offset address/load/store slice.
pub(crate) fn fold_emitted_copy_ops(nodes: &[InstrNode]) -> Option<Vec<MirMemOp>> {
    let mut env: HashMap<ValueId, AddrVal> = HashMap::new();
    // Loaded value `ValueId` -> (source base, source byte offset, width).
    let mut loaded: HashMap<ValueId, (ValueId, u64, u32)> = HashMap::new();
    let mut ops: Vec<MirMemOp> = Vec::new();

    for node in nodes {
        match fold_addr_step(&mut env, node)? {
            true => continue,
            false => {}
        }
        match &node.inst {
            // A lane load: record WHICH source cell this value came from. Do NOT
            // emit a `MirMemOp::Load` (stores-only model).
            Inst::Load { ty, ptr, .. } => {
                let AddrVal::Ptr { base, off } = lookup(&env, *ptr) else {
                    return None;
                };
                let width = scalar_byte_width(ty)?;
                let offset = u64::try_from(off).ok()?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                loaded.insert(*result, (base, offset, width));
            }

            // A lane store: its value MUST be a value loaded earlier in the slice
            // (a pure copy). Name the stored value by its SOURCE cell so the dst
            // cell is proven to hold the original src contents.
            Inst::Store {
                ty, ptr, value, ..
            } => {
                let AddrVal::Ptr {
                    base: dst_base,
                    off: dst_off,
                } = lookup(&env, *ptr)
                else {
                    return None;
                };
                let width = scalar_byte_width(ty)?;
                let dst_off = u64::try_from(dst_off).ok()?;
                // Not a copied (previously-loaded) value -> not the copy shape.
                let (src_base, src_off, src_width) = *loaded.get(value)?;
                // A lane that loads and stores at mismatched widths is out of slice.
                if src_width != width {
                    return None;
                }
                // src and dst sharing a base is an in-place/overlapping copy whose
                // "original contents" naming would be unsound — skip it.
                if src_base == dst_base {
                    return None;
                }
                ops.push(MirMemOp::Store {
                    addr: MemAddr {
                        base: mem_base_name(dst_base),
                        offset: dst_off,
                    },
                    value: SmtExpr::var(mem_lane_name(src_base, src_off), width * 8),
                    width,
                });
            }

            _ => return None,
        }
    }
    Some(ops)
}

// ===========================================================================
// `<[T]>::split_at` / `str::split_at` VALUE-level refinement
// ===========================================================================
//
// Unlike the field LOAD/STORE/COPY lanes above (which model the emitted MEMORY
// op SEQUENCE against a layout spec), `split_at` writes its two `{data,len}`
// halves through `InsertField`s into the destination tuple slot — there is no
// byte-addressed load/store sequence to fold. Instead this lane reconstructs the
// two halves' VALUES (and the bounds-check trap predicate) SYMBOLICALLY from the
// exact trust-ir the bridge EMITTED (`ICmp` + `emit_element_addr`'s Mul/Add +
// the `Sub` + the `InsertField` value operands), naming the receiver's
// `ptr`/`len`/`mid` (external values the slice never defines) by their `ValueId`.
// The SPEC side (`mir_semantics::split_at_spec`) re-derives the SAME halves from
// the Rust definition over the SAME symbolic names. The two meet only on those
// names — so a bridge that swaps `mid`/`len`, scales by the wrong element size,
// computes `mid - len`, or inverts the bounds `ICmp` folds to a genuinely
// different formula and REFUTES. A shape the fold does not recognise (a missing
// bounds check, an unexpected instruction) returns `None` — the statement is
// SKIPPED, never guessed at (sound: less coverage, never a wrong verdict).

/// Canonical symbolic 64-bit name for a `ValueId` the split_at slice reads but
/// never defines (the receiver `ptr`/`len`/`mid`, the destination slot pointer).
/// SHARED by the IMPL fold and the SPEC-pairing obligation builder (which names
/// the spec's `ptr`/`len`/`mid` via this function), so a CORRECT lowering anchors
/// both sides on the same symbolic values while a bridge that reads a DIFFERENT
/// `ValueId` (a swapped operand) names a distinct var and REFUTES.
pub(crate) fn sa_value_name(v: ValueId) -> String {
    format!("sa_v{}", v.index())
}

/// Canonical symbolic 64-bit name for the PRE-state value a folded `Load` read
/// from `base + off` (the Range::next state-transition lane's `Inst::Load ->
/// symbolic pre-state` primitive). SHARED by the IMPL fold (which binds each
/// emitted `Load`'s result to this symbol) and the SPEC-pairing obligation
/// builder (which names the spec's `start`/`end` via this function over the SELF
/// slot base + field offsets), so a CORRECT lowering anchors both sides on the
/// same pre-state symbols while a bridge that loads a DIFFERENT field (a swapped
/// `start`/`end`) names a distinct var and REFUTES.
pub(crate) fn ld_value_name(base: ValueId, off: u64) -> String {
    format!("ld_v{}_o{}", base.index(), off)
}

/// Canonical symbolic 64-bit name for the PRE-state value a folded NARROW
/// `Load` (`width` in `{1, 2, 4}` bytes) read from `base + off` — the lane-11
/// WIDTH-FAITHFUL primitive. The symbol is declared 64-bit but the folded VALUE
/// is `var & mask(width)` (its low `width` bytes), matching the machine: a
/// `w`-byte load reads exactly `w` bytes (trust-ir `interpret.rs::eval_load`
/// reads `byte_size(ty)` bytes; the decoded `InterpretInt.raw` is masked to
/// `bits`). The WIDTH is part of the name so an 8-byte load of the same cell
/// (`ld_value_name`, kept for lanes 7/9 backward compatibility) can never
/// alias a narrow one.
pub(crate) fn ld_value_name_w(base: ValueId, off: u64, width: u32) -> String {
    format!("ld_v{}_o{}_w{}", base.index(), off, width)
}

/// A folded value in the split_at symbolic evaluator. `Int`/`Ptr` keep the
/// base-plus-constant-offset structure the address arithmetic needs (so the
/// `InsertField` destination OFFSET into the tuple slot is recoverable exactly);
/// `Expr`/`Bool` carry a general reconstructed formula (a right-half data/len
/// value, or the bounds predicate).
#[derive(Clone)]
enum Sv {
    /// A known integer constant (an offset, an element index, the element size).
    Int(i128),
    /// `base + off` bytes — a pointer, or its `PtrToInt` integer image (the two
    /// denote the SAME 64-bit value). `base` is a `ValueId` the slice never
    /// defines (named `sa_v{base}`); `off` is a reconstructed CONSTANT byte offset.
    Ptr { base: ValueId, off: i128 },
    /// A general 64-bit value expression (right-half arithmetic over the inputs).
    Expr(SmtExpr),
    /// A folded `ICmp` result (a 1-bit predicate whose value is captured
    /// separately as the bounds predicate). Marks a value that may be used ONLY as
    /// the bounds predicate — never as a 64-bit arithmetic/store operand, which
    /// takes the fold out of slice (`sv_bv` / a `Cast` of a `Bool` bails).
    Bool,
}

/// Resolve an operand through the fold environment; a `ValueId` the slice never
/// defines is the external base/input it names symbolically at offset 0.
fn lookup_sv(env: &HashMap<ValueId, Sv>, v: ValueId) -> Sv {
    env.get(&v).cloned().unwrap_or(Sv::Ptr { base: v, off: 0 })
}

/// Bind the single result of `node` to `val`. `None` if the instruction does not
/// have exactly one result (out of slice).
fn bind_sv(env: &mut HashMap<ValueId, Sv>, node: &InstrNode, val: Sv) -> Option<()> {
    let [result] = node.results.as_slice() else {
        return None;
    };
    env.insert(*result, val);
    Some(())
}

/// Register `base`'s symbolic 64-bit name in `inputs` (once) and return its var.
fn sa_input_var(inputs: &mut Vec<(String, u32)>, base: ValueId) -> SmtExpr {
    let name = sa_value_name(base);
    if !inputs.iter().any(|(n, _)| n == &name) {
        inputs.push((name.clone(), 64));
    }
    SmtExpr::var(name, 64)
}

/// Lower an `Sv` to its 64-bit `SmtExpr`, registering any external base it names.
/// A `Bool` has no 64-bit image — an `ICmp` result flowing into arithmetic is out
/// of the split_at slice, so this bails the fold.
fn sv_bv(inputs: &mut Vec<(String, u32)>, sv: Sv) -> Option<SmtExpr> {
    Some(match sv {
        Sv::Int(v) => SmtExpr::bv_const(v as u64, 64),
        Sv::Ptr { base, off } => {
            let e = sa_input_var(inputs, base);
            if off == 0 {
                e
            } else {
                e.bvadd(SmtExpr::bv_const(off as u64, 64))
            }
        }
        Sv::Expr(e) => e,
        Sv::Bool => return None,
    })
}

/// `a + b`: keep `base + const` structure when possible (address arithmetic),
/// else fall back to a general `bvadd`.
fn sv_add(inputs: &mut Vec<(String, u32)>, a: Sv, b: Sv) -> Option<Sv> {
    Some(match (a, b) {
        (Sv::Ptr { base, off }, Sv::Int(k)) | (Sv::Int(k), Sv::Ptr { base, off }) => Sv::Ptr {
            base,
            off: off.checked_add(k)?,
        },
        (Sv::Int(x), Sv::Int(y)) => Sv::Int(x.checked_add(y)?),
        (a, b) => Sv::Expr(sv_bv(inputs, a)?.bvadd(sv_bv(inputs, b)?)),
    })
}

/// `a - b`.
fn sv_sub(inputs: &mut Vec<(String, u32)>, a: Sv, b: Sv) -> Option<Sv> {
    Some(match (a, b) {
        (Sv::Ptr { base, off }, Sv::Int(k)) => Sv::Ptr {
            base,
            off: off.checked_sub(k)?,
        },
        (Sv::Int(x), Sv::Int(y)) => Sv::Int(x.checked_sub(y)?),
        (a, b) => Sv::Expr(sv_bv(inputs, a)?.bvsub(sv_bv(inputs, b)?)),
    })
}

/// `a * b`.
fn sv_mul(inputs: &mut Vec<(String, u32)>, a: Sv, b: Sv) -> Option<Sv> {
    Some(match (a, b) {
        (Sv::Int(x), Sv::Int(y)) => Sv::Int(x.checked_mul(y)?),
        (a, b) => Sv::Expr(sv_bv(inputs, a)?.bvmul(sv_bv(inputs, b)?)),
    })
}

/// The boolean predicate for a folded `ICmp` over reconstructed operands.
fn icmp_bool(op: ICmpOp, l: SmtExpr, r: SmtExpr) -> SmtExpr {
    match op {
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
    }
}

/// The boolean predicate for a folded `ICmp` at BYTE WIDTH `w` over
/// ALREADY-`w`-MASKED 64-bit operands (lane 13 — the narrow `Range::next`
/// compare; used ONLY by `fold_emitted_range_next`). `w == 8` is EXACTLY
/// [`icmp_bool`] (no behavior change for any landed 64-bit lane). At `w` in
/// `{1, 2, 4}` the machine compares the `w`-byte values (trust-ir
/// `interpret.rs::eval_int_icmp`):
///   * UNSIGNED ops (and `Eq`/`Ne`) compare the raw masked bits
///     (`ICmpOp::Ult => lhs.raw < rhs.raw`) — the direct 64-bit compare of
///     the masked operands is equal semantics;
///   * SIGNED ops decode two's complement at `w` and compare the decoded
///     integers (`ICmpOp::Slt => lhs.as_signed() < rhs.as_signed()`, where
///     `as_signed` subtracts `2^bits` when the sign bit is set) — modeled by
///     sign-EXTENDING the masked operand to 64 bits,
///     `sext_w(x) = (x ^ sign_w) - sign_w` with `sign_w = 2^(8w-1)`, then the
///     64-bit signed compare (identical ordering).
fn icmp_bool_w(op: ICmpOp, w: u32, l: SmtExpr, r: SmtExpr) -> SmtExpr {
    if w == 8 {
        return icmp_bool(op, l, r);
    }
    debug_assert!(matches!(w, 1 | 2 | 4), "narrow icmp width {w}");
    match op {
        ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge => {
            let sign = SmtExpr::bv_const(1u64 << (8 * w - 1), 64);
            let sext = |x: SmtExpr| x.bvxor(sign.clone()).bvsub(sign.clone());
            icmp_bool(op, sext(l), sext(r))
        }
        _ => icmp_bool(op, l, r),
    }
}

/// Lower an operand of a WIDTH-`w` op inside `fold_emitted_range_next` to a
/// 64-bit expression PROVABLY equal to the machine's `w`-byte value (lane 13).
/// Accepts ONLY:
///   * a reconstructed CONSTANT — masked defensively to `w` bytes: the machine
///     value of a `w`-wide `Const` is its low `w` bytes (trust-ir
///     `interpret.rs`: `InterpretInt::from_i128` masks `value` to `bits`), so
///     the masked model is faithful for every constant, negatives included;
///   * an in-slice value RECORDED masked-at-`w` in `narrow_w` (a narrow load /
///     narrow add / narrow Select of exactly this width).
/// ANYTHING else returns `None` and bails the fold (skip, sound): an unmasked
/// 64-bit value (an 8-byte load symbol, an external base) flowing into a
/// narrow compare/select would make the masked model diverge from the machine
/// on the high bits — the lane-9 width class — so it stays out of slice.
fn narrow_masked_operand(
    env: &HashMap<ValueId, Sv>,
    narrow_w: &HashMap<ValueId, u32>,
    v: ValueId,
    w: u32,
) -> Option<SmtExpr> {
    match lookup_sv(env, v) {
        Sv::Int(k) => Some(SmtExpr::bv_const(
            ((k as u128) & u128::from(low_bytes_mask(w))) as u64,
            64,
        )),
        Sv::Expr(e) if narrow_w.get(&v) == Some(&w) => Some(e),
        _ => None,
    }
}

/// The bridge's reconstructed `split_at`: the bounds "continue" predicate and the
/// emitted `{data,len}` field stores into the destination tuple slot.
pub(crate) struct SplitAtFolded {
    /// The reconstructed bounds "continue" (no-trap) predicate — the emitted
    /// bounds `ICmp`'s comparison over the symbolic `mid`/`len`. The bridge
    /// branches to the split's normal target when this holds and TRAPS otherwise.
    ok: SmtExpr,
    /// The emitted fat-ptr field stores as `(dest byte offset, lane, value)` — one
    /// per `InsertField` the bridge performed into the destination tuple slot
    /// (lane 0 = data, lane 1 = len). All share the one destination base.
    stores: Vec<(u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references.
    inputs: Vec<(String, u32)>,
}

impl SplitAtFolded {
    /// The value stored into the tuple slot at byte `offset`, lane `lane`.
    fn store_value(&self, offset: u64, lane: u32) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(o, l, _)| *o == offset && *l == lane)
            .map(|(_, _, v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a `split_at` lowering (the bounds `ICmp`, the
/// `emit_element_addr` Mul/Add for the right half's data pointer, the `Sub` for
/// its length, and the four `InsertField`s that write the two `{data,len}` halves
/// into the destination tuple slot) into a [`SplitAtFolded`].
///
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`InsertField` — never a re-derivation from
/// the spec — so a wrong emitted formula produces a wrong folded value here and
/// the obligation against the layout-independent spec REFUTES (the anti-tautology
/// guarantee). Returns `None` (skip the statement, sound) for ANY instruction
/// outside this slice, a missing bounds check (`ok` never set), or destination
/// stores that do not all share the one tuple-slot base.
pub(crate) fn fold_emitted_split_at(nodes: &[InstrNode]) -> Option<SplitAtFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut ok: Option<SmtExpr> = None;
    // (dest base, byte offset, lane, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr` /
            // `coerce_to_i64`): propagate the operand value.
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The (single) bounds-check `ICmp` -> the continue predicate. Its
            // result feeds a `CondBr` outside the folded slice; it is bound as a
            // `Bool` so that a (malformed) shape flowing an `ICmp` result into
            // arithmetic / a store value bails the fold (`sv_bv`/`Cast` reject a
            // `Bool`), never mis-folding it as an external pointer.
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                if ok.is_some() {
                    return None; // more than one comparison is out of shape
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                ok = Some(icmp_bool(*op, l, r));
                bind_sv(&mut env, node, Sv::Bool)?;
            }

            // A fat-ptr field store into the destination tuple slot. The aggregate
            // operand is `dest_base + const_offset`; the value is a reconstructed
            // 64-bit half field. The `InsertField` result is not read further.
            Inst::InsertField {
                aggregate,
                field,
                value,
                ..
            } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *aggregate) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, *field, val));
            }

            // Anything else is out of the split_at fold slice.
            _ => return None,
        }
    }

    let ok = ok?;
    // Every store must target the SAME destination base (the split tuple slot).
    let base0 = stores.first()?.0;
    if !stores.iter().all(|(b, ..)| *b == base0) {
        return None;
    }
    let stores = stores.into_iter().map(|(_, o, f, v)| (o, f, v)).collect();
    Some(SplitAtFolded { ok, stores, inputs })
}

/// The bridge's reconstructed slice-to-Vec `{ptr, cap, len}` header (TV lane 14).
pub(crate) struct SliceToVecHeaderFolded {
    /// The capacity the bridge ACTUALLY computed (its `n >u 1 ? n : 1` Select).
    pub(crate) cap: SmtExpr,
    /// The byte count the bridge ACTUALLY passed as `__rust_alloc`'s first arg.
    pub(crate) alloc_bytes: SmtExpr,
    /// The alignment the bridge ACTUALLY passed as `__rust_alloc`'s second arg.
    pub(crate) alloc_align: SmtExpr,
    /// `(field, value)` for each `InsertField` into the header slot.
    pub(crate) stores: Vec<(u32, SmtExpr)>,
    /// The `ValueId` `__rust_alloc` defined, so the `ptr` field store can be
    /// checked to hold THAT result and not some other pointer.
    pub(crate) alloc_result: ValueId,
    /// Symbolic 64-bit inputs the reconstruction references.
    pub(crate) inputs: Vec<(String, u32)>,
}

impl SliceToVecHeaderFolded {
    /// The value stored into header field `field`, if any.
    pub(crate) fn store_value(&self, field: u32) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(f, _)| *f == field)
            .map(|(_, v)| v.clone())
    }
}

/// The exact node count of `lower_slice_to_vec`'s header window
/// (`Alloca`, `Const 1`, `ICmp Ugt`, `Select`, `Const size`, `Mul`,
/// `Const align`, `Call __rust_alloc`, and three `InsertField`s).
pub(crate) const SLICE_TO_VEC_HEADER_NODES: usize = 11;

/// Fold the EMITTED trust-ir of a slice-to-Vec header into a
/// [`SliceToVecHeaderFolded`] (TV lane 14).
///
/// # Why the shape is PINNED rather than matched arm-by-arm
///
/// The adversarial panel's second finding was that every STRUCTURAL wrong
/// emission in this lane degrades to a SILENT SKIP — including the brief's own
/// named mutant, "the header stored to a stale base". An arm-by-arm fold that
/// simply returns `None` on anything unexpected cannot distinguish "this is not
/// a to_vec" from "this IS a to_vec and it is emitted WRONG", so a real defect
/// and a benign refactor look identical, and the lane quietly stops covering the
/// construct it was written for.
///
/// Pinning `nodes.len() == SLICE_TO_VEC_HEADER_NODES` makes a shape drift a
/// hard, testable fact instead of an arm-by-arm fall-through. Callers report
/// whether the lane FIRED (see `MemRefineKind::SliceToVecHeader`), so a lane that
/// stops firing is visible rather than silently absent.
///
/// # Anti-tautology
///
/// Every value here is reconstructed from the REAL emitted
/// `Const`/`ICmp`/`Select`/`Mul`/`Call`/`InsertField` — never re-derived from
/// the spec. The capacity comes from the emitted `Select`, the alloc size and
/// alignment from the ACTUAL `__rust_alloc` argument list, and the header fields
/// from the ACTUAL `InsertField`s. The spec states capacity in a deliberately
/// different canonical form, so the two meet only on the shared name for `n`.
///
/// # Trusted-model boundary
///
/// The `InsertField`s are read with the ADAPTER's store semantics (an
/// `InsertField` over a `Ptr` aggregate writes the field lane of the pointed-to
/// slot). trust-ir's REFERENCE interpreter rejects that form as ill-typed, so
/// this lane's soundness is relative to the adapter's interpretation — stated
/// here rather than left implicit.
pub(crate) fn fold_emitted_slice_to_vec_header(
    nodes: &[InstrNode],
) -> Option<SliceToVecHeaderFolded> {
    // SHAPE PIN — see the note above. Must be the first thing checked.
    if nodes.len() != SLICE_TO_VEC_HEADER_NODES {
        return None;
    }

    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut cap: Option<SmtExpr> = None;
    let mut alloc: Option<(ValueId, SmtExpr, SmtExpr)> = None;
    let mut slot_base: Option<ValueId> = None;
    let mut stores: Vec<(ValueId, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            // The header slot. `Alloca` defines a FRESH base the slice itself
            // owns; bind it at offset 0 so the `InsertField`s resolve to it.
            Inst::Alloca { .. } => {
                let result = node.results.first().copied()?;
                if slot_base.is_some() {
                    return None; // a second Alloca is out of shape
                }
                slot_base = Some(result);
                bind_sv(
                    &mut env,
                    node,
                    Sv::Ptr {
                        base: result,
                        off: 0,
                    },
                )?;
            }

            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // The `cap = n >u 1 ? n : 1` guard compare. Captured as `Bool` so it
            // can only be consumed by the Select.
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let _ = icmp_bool(*op, l, r);
                bind_sv(&mut env, node, Sv::Bool)?;
            }

            // The capacity itself. Reconstructed from the EMITTED arms.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow select truncates
                }
                if !matches!(lookup_sv(&env, *cond), Sv::Bool) {
                    return None; // the condition must be the folded compare
                }
                if cap.is_some() {
                    return None; // a second Select is out of shape
                }
                let t = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let e = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                // Rebuild the emission's own shape: `cond ? then : else`. The
                // SPEC states max(n,1) canonically instead, so the two agree
                // only if the emission really computes a maximum.
                let value = SmtExpr::ite(emitted_ugt_guard(&env, nodes)?, t, e);
                cap = Some(value.clone());
                bind_sv(&mut env, node, Sv::Expr(value))?;
            }

            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The allocation. Its ARGUMENTS are the size/align obligations, and
            // its RESULT is the pointer the header must record.
            Inst::Call { args, .. } => {
                if alloc.is_some() || args.len() != 2 {
                    return None;
                }
                let result = node.results.first().copied()?;
                let bytes = sv_bv(&mut inputs, lookup_sv(&env, args[0]))?;
                let align = sv_bv(&mut inputs, lookup_sv(&env, args[1]))?;
                alloc = Some((result, bytes, align));
                // The returned buffer is a fresh symbolic base. NOTE: this lane
                // does NOT prove freshness — see the module spec's
                // trusted-model-boundary note.
                bind_sv(
                    &mut env,
                    node,
                    Sv::Ptr {
                        base: result,
                        off: 0,
                    },
                )?;
            }

            Inst::InsertField {
                aggregate,
                field,
                value,
                ..
            } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *aggregate) else {
                    return None;
                };
                if off != 0 {
                    return None; // the header is written at the slot base
                }
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, *field, val));
            }

            // Anything else is out of the to_vec header slice.
            _ => return None,
        }
    }

    let (alloc_result, alloc_bytes, alloc_align) = alloc?;
    let cap = cap?;
    let slot_base = slot_base?;
    // D4: exactly three stores, pairwise-distinct fields, ALL into the header
    // slot the Alloca defined (never a stale or foreign base).
    if stores.len() != 3 || !stores.iter().all(|(b, ..)| *b == slot_base) {
        return None;
    }
    let mut fields: Vec<u32> = stores.iter().map(|(_, f, _)| *f).collect();
    fields.sort_unstable();
    fields.dedup();
    if fields.len() != 3 {
        return None;
    }
    let stores = stores.into_iter().map(|(_, f, v)| (f, v)).collect();
    Some(SliceToVecHeaderFolded {
        cap,
        alloc_bytes,
        alloc_align,
        stores,
        alloc_result,
        inputs,
    })
}

/// Rebuild the emitted `n >u 1` guard as an SMT predicate, from the ICmp the
/// window actually contains. Kept separate so the `Select` arm reconstructs the
/// emission's real condition rather than assuming one.
fn emitted_ugt_guard(env: &HashMap<ValueId, Sv>, nodes: &[InstrNode]) -> Option<SmtExpr> {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for node in nodes {
        if let Inst::ICmp { op, lhs, rhs, .. } = &node.inst {
            let l = sv_bv(&mut inputs, lookup_sv(env, *lhs))?;
            let r = sv_bv(&mut inputs, lookup_sv(env, *rhs))?;
            return Some(icmp_bool(*op, l, r));
        }
    }
    None
}

/// Pair the reconstructed bridge header (`folded`) with the Rust
/// [`slice_to_vec_header_spec`] over the SAME symbolic name for `n`, and build
/// the refinement obligations (TV lane 14).
///
/// # Which facts are SMT obligations and which are structural
///
/// The `ptr` field is checked STRUCTURALLY — the value stored must be the
/// `ValueId` `__rust_alloc` defined — rather than as an SMT equation. The
/// rejected design made it an obligation whose spec side was *defined as* the
/// folded value, which is circular (`sa_vK == sa_vK` for any emission). A
/// structural identity check has real content; a self-referential equation does
/// not.
///
/// `cap`, `alloc_bytes`, `alloc_align` and the `cap`/`len` field stores ARE
/// obligations, because their spec sides are built independently: capacity from
/// the canonical `ITE(n == 0, 1, n)`, size/align from the LAYOUT ORACLE, and
/// length from the shared symbol for `n`. An emission that stores capacity into
/// the length field (or vice versa) yields a different folded formula and
/// REFUTES.
///
/// Returns `None` (skip, sound) if any header field is missing or the `ptr`
/// field does not hold the allocation result.
pub(crate) fn slice_to_vec_header_obligations(
    name: &str,
    folded: &SliceToVecHeaderFolded,
    n: ValueId,
    elem_size: u64,
    elem_align: u64,
    field_ptr: u32,
    field_cap: u32,
    field_len: u32,
) -> Option<Vec<ProofObligation>> {
    let spec = trust_cg_verify::mir_semantics::slice_to_vec_header_spec(
        &sa_value_name(n),
        elem_size,
        elem_align,
    );

    // STRUCTURAL: the ptr field must hold the allocation's own result.
    let stored_ptr = folded.store_value(field_ptr)?;
    let expected_ptr = SmtExpr::var(sa_value_name(folded.alloc_result), 64);
    if format!("{stored_ptr:?}") != format!("{expected_ptr:?}") {
        return None;
    }

    let stored_cap = folded.store_value(field_cap)?;
    let stored_len = folded.store_value(field_len)?;
    let inputs = &folded.inputs;

    Some(vec![
        // The capacity the bridge computed is max(n,1) — spec stated canonically,
        // emission stated as `n >u 1 ? n : 1`.
        split_at_obligation(name, "cap", folded.cap.clone(), spec.cap.clone(), inputs),
        // The bytes requested from the allocator match cap * elem_size, with
        // elem_size from the layout oracle.
        split_at_obligation(
            name,
            "alloc_bytes",
            folded.alloc_bytes.clone(),
            spec.alloc_bytes,
            inputs,
        ),
        // The alignment requested matches the layout oracle's.
        split_at_obligation(
            name,
            "alloc_align",
            folded.alloc_align.clone(),
            spec.alloc_align,
            inputs,
        ),
        // The cap FIELD records that same capacity (not, say, n).
        split_at_obligation(name, "header_cap", stored_cap, spec.cap, inputs),
        // The len FIELD records n (not the capacity).
        split_at_obligation(name, "header_len", stored_len, spec.len, inputs),
    ])
}

/// A named split_at value-refinement obligation and its bridge/spec sides
/// (`trust_ir_expr` = the folded bridge value, `aarch64_expr` = the spec value).
fn split_at_obligation(
    name: &str,
    sub: &str,
    bridge: SmtExpr,
    spec: SmtExpr,
    inputs: &[(String, u32)],
) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name: format!("{name}_{sub}"),
        trust_ir_expr: bridge,
        aarch64_expr: spec,
        inputs: inputs.to_vec(),
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        // A MIR->trust-ir value-preservation VC at the interception boundary.
        category: Some(TransvalCheckKind::DataFlow),
    }
}

/// Pair the reconstructed bridge `split_at` (`folded`) with the Rust
/// [`split_at_spec`] over the SAME symbolic `ptr`/`len`/`mid` names and build the
/// five refinement obligations:
///   * `trap`     — the bridge traps (takes the non-`ok` edge) IFF `mid >u len`;
///   * `fst_data` — the half stored at `off0` lane 0 equals `ptr`;
///   * `fst_len`  — `off0` lane 1 equals `mid`;
///   * `snd_data` — `off1` lane 0 equals `ptr + mid*elem_size`;
///   * `snd_len`  — `off1` lane 1 equals `len - mid`.
///
/// `off0`/`off1` are the destination tuple's two `{data,len}` field byte offsets
/// (the layout the bridge stored through); `ptr`/`len`/`mid` are the receiver's
/// data-pointer / length / split-index `ValueId`s (named via [`sa_value_name`],
/// matching the fold). Returns `None` when the reconstructed stores do not cover
/// the two halves' lanes (a shape mismatch — fail closed, never a wrong verdict).
#[allow(clippy::too_many_arguments)]
pub(crate) fn split_at_obligations(
    name: &str,
    folded: &SplitAtFolded,
    off0: u64,
    off1: u64,
    ptr: ValueId,
    len: ValueId,
    mid: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: SplitAtSpec = split_at_spec(
        &sa_value_name(ptr),
        &sa_value_name(len),
        &sa_value_name(mid),
        elem_size,
    );

    let fst_data = folded.store_value(off0, 0)?;
    let fst_len = folded.store_value(off0, 1)?;
    let snd_data = folded.store_value(off1, 0)?;
    let snd_len = folded.store_value(off1, 1)?;

    // Declare every symbolic name either side references: the fold names
    // `ptr`/`len`/`mid` identically to the spec, so `folded.inputs` normally
    // already covers `spec.inputs`; union them anyway so an edge emission that
    // referenced a receiver value only on the spec side is still fully declared.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(n, _)| n == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // Trap predicate as a 1-bit BV (matching the bridge's `ICmp`+`CondBr` edge):
    // the bridge traps on the NON-`ok` edge; the spec traps iff `mid >u len`. The
    // two are complementary comparisons — structurally distinct (non-vacuous),
    // equivalent only when the emitted bounds check is exactly `mid <= len`.
    let one = SmtExpr::bv_const(1, 1);
    let zero = SmtExpr::bv_const(0, 1);
    let bridge_trap = SmtExpr::ite(folded.ok.clone(), zero.clone(), one.clone());
    let spec_trap = SmtExpr::ite(spec.trap.clone(), one, zero);

    Some(vec![
        split_at_obligation(name, "trap", bridge_trap, spec_trap, inputs),
        split_at_obligation(name, "fst_data", fst_data, spec.fst_data, inputs),
        split_at_obligation(name, "fst_len", fst_len, spec.fst_len, inputs),
        split_at_obligation(name, "snd_data", snd_data, spec.snd_data, inputs),
        split_at_obligation(name, "snd_len", snd_len, spec.snd_len, inputs),
    ])
}

// ===========================================================================
// `<[T]>::chunks / windows / chunks_exact / rchunks / rchunks_exact`
// stride-iterator CONSTRUCTOR VALUE-level refinement
// ===========================================================================
//
// The bridge lowers `v.chunks(n)` (and the four siblings) over a `&[T]` receiver
// into a `{ ptr@0 = data, end@8 = data + len*elem_size, n@16 = n }` cursor written
// through THREE typed `Store`s into the destination slot, guarded by an `ICmp
// Ne(n, 0)` (std's "chunk/window size must be non-zero" panic — the class the
// `chunks(0)` infinite-loop bug lived in). This lane reconstructs the trap
// predicate + the three cursor field VALUES SYMBOLICALLY from the exact trust-ir
// the bridge EMITTED (`emit_element_addr`'s Mul/Add for `end`, the `ICmp`, and the
// three `emit_typed_store`s), naming the receiver's `data`/`len`/`n` (external
// values the slice never defines) by their `ValueId`. The SPEC side
// (`mir_semantics::stride_iter_ctor_spec`) re-derives the SAME cursor from the Rust
// definition over the SAME symbolic names. The two meet only on those names — so a
// bridge that drops/inverts the `n != 0` check, scales `end` by the wrong element
// size, computes `end` off the wrong base, or swaps the cursor fields folds to a
// genuinely different formula and REFUTES. A shape the fold does not recognise (a
// MISSING `n != 0` check, an unexpected instruction) returns `None` — the statement
// is SKIPPED, never guessed at (sound: less coverage, never a wrong verdict).
//
// This reuses the `split_at` `Sv`/`sv_*`/`sa_value_name`/`icmp_bool` machinery
// verbatim; the only structural difference is that the cursor is written through
// typed `Store`s (not `InsertField`s), so the fold reconstructs `(dest offset,
// value)` pairs from the emitted `Store` address arithmetic.

/// The bridge's reconstructed stride-iterator constructor: the `n != 0` "continue"
/// (no-trap) predicate and the emitted `{ ptr, end, n }` cursor field stores.
pub(crate) struct StrideIterCtorFolded {
    /// The reconstructed "continue" (no-trap) predicate — the emitted `n != 0`
    /// `ICmp`'s comparison. The bridge branches to the constructor's normal target
    /// when this holds and TRAPS (the non-zero-stride panic) otherwise.
    ok: SmtExpr,
    /// The emitted cursor field stores as `(dest byte offset, value)` — one per
    /// `emit_typed_store` into the destination slot. All share the one dest base.
    stores: Vec<(u64, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references.
    inputs: Vec<(String, u32)>,
}

impl StrideIterCtorFolded {
    /// The value stored into the cursor slot at byte `offset`.
    fn store_value(&self, offset: u64) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(o, _)| *o == offset)
            .map(|(_, v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a stride-iterator constructor lowering (the
/// `emit_element_addr` Mul/Add for `end`, the `ICmp Ne(n, 0)`, and the three
/// `emit_typed_store`s that write `{ ptr, end, n }` into the destination cursor
/// slot) into a [`StrideIterCtorFolded`].
///
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`Store` — never a re-derivation from the
/// spec — so a wrong emitted formula produces a wrong folded value here and the
/// obligation against the layout-independent spec REFUTES (the anti-tautology
/// guarantee). Returns `None` (skip the statement, sound) for ANY instruction
/// outside this slice, a MISSING non-zero check (`ok` never set), or cursor stores
/// that do not all share the one destination-slot base.
pub(crate) fn fold_emitted_stride_iter_ctor(nodes: &[InstrNode]) -> Option<StrideIterCtorFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut ok: Option<SmtExpr> = None;
    // (dest base, byte offset, value).
    let mut stores: Vec<(ValueId, u64, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr` /
            // `coerce_to_i64`): propagate the operand value.
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The (single) `n != 0` `ICmp` -> the continue predicate. Its result
            // feeds a `CondBr` outside the folded slice; it is bound as a `Bool` so
            // a (malformed) shape flowing an `ICmp` result into arithmetic / a store
            // value bails the fold (`sv_bv`/`Cast` reject a `Bool`), never
            // mis-folding it as an external pointer.
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                if ok.is_some() {
                    return None; // more than one comparison is out of shape
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                ok = Some(icmp_bool(*op, l, r));
                bind_sv(&mut env, node, Sv::Bool)?;
            }

            // A cursor field store into the destination slot. The address is
            // `dest_base + const_offset`; the value is a reconstructed 64-bit field.
            // The `Store` has no result to bind.
            Inst::Store { ptr, value, .. } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, val));
            }

            // Anything else is out of the stride-iter-ctor fold slice.
            _ => return None,
        }
    }

    let ok = ok?; // a MISSING non-zero check -> None (fail-closed skip)
    // Every store must target the SAME destination base (the cursor slot).
    let base0 = stores.first()?.0;
    if !stores.iter().all(|(b, ..)| *b == base0) {
        return None;
    }
    let stores = stores.into_iter().map(|(_, o, v)| (o, v)).collect();
    Some(StrideIterCtorFolded { ok, stores, inputs })
}

/// Pair the reconstructed bridge stride-iter constructor (`folded`) with the Rust
/// [`stride_iter_ctor_spec`] over the SAME symbolic `data`/`len`/`n` names and
/// build the four CORE refinement obligations:
///   * `trap` — the bridge traps (takes the non-`ok` edge) IFF `n == 0`;
///   * `ptr`  — the value stored at `ptr_off` equals `data`;
///   * `end`  — the value stored at `end_off` equals `data + len*elem_size`;
///   * `n`    — the value stored at `n_off` equals `n`.
///
/// `ptr_off`/`end_off`/`n_off` are the cursor's three field byte offsets (the
/// layout the bridge stored through — `0` / `SLICE_ITER_END_OFFSET` /
/// `WINDOWS_SIZE_OFFSET`); `data`/`len`/`n` are the receiver's data-pointer /
/// length / stride `ValueId`s (named via [`sa_value_name`], matching the fold).
/// Returns `None` when the reconstructed stores do not cover the three cursor
/// fields (a shape mismatch — fail closed, never a wrong verdict).
///
/// The `*_exact` remainder fields (offsets 24/32) are OUT OF SCOPE: the fold's
/// slice ends at the third cursor store, so a `*_exact` construction is refined on
/// its CORE cursor + trap exactly like the non-exact variants, ABSTAINING on the
/// remainder (never claimed, never falsely Refined).
#[allow(clippy::too_many_arguments)]
pub(crate) fn stride_iter_ctor_obligations(
    name: &str,
    folded: &StrideIterCtorFolded,
    ptr_off: u64,
    end_off: u64,
    n_off: u64,
    data: ValueId,
    len: ValueId,
    n: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: StrideIterCtorSpec = stride_iter_ctor_spec(
        &sa_value_name(data),
        &sa_value_name(len),
        &sa_value_name(n),
        elem_size,
    );

    let cur_ptr = folded.store_value(ptr_off)?;
    let cur_end = folded.store_value(end_off)?;
    let cur_n = folded.store_value(n_off)?;

    // Declare every symbolic name either side references: the fold names
    // `data`/`len`/`n` identically to the spec, so `folded.inputs` normally already
    // covers `spec.inputs`; union them anyway so an emission that referenced a
    // receiver value only on the spec side is still fully declared.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // Trap predicate as a 1-bit BV (matching the bridge's `ICmp`+`CondBr` edge):
    // the bridge traps on the NON-`ok` edge; the spec traps iff `n == 0`. The two
    // are complementary comparisons — structurally distinct (non-vacuous),
    // equivalent only when the emitted check is exactly `n != 0`.
    let one = SmtExpr::bv_const(1, 1);
    let zero = SmtExpr::bv_const(0, 1);
    let bridge_trap = SmtExpr::ite(folded.ok.clone(), zero.clone(), one.clone());
    let spec_trap = SmtExpr::ite(spec.trap.clone(), one, zero);

    Some(vec![
        split_at_obligation(name, "trap", bridge_trap, spec_trap, inputs),
        split_at_obligation(name, "ptr", cur_ptr, spec.ptr, inputs),
        split_at_obligation(name, "end", cur_end, spec.end, inputs),
        split_at_obligation(name, "n", cur_n, spec.n, inputs),
    ])
}

// ===========================================================================
// `<Vec<T> as Index>::index` / `index_mut` and `<[T]>::index` CHECKED-INDEX
// (`v[i]` / `&v[i]` / `&mut v[i]`) VALUE-level refinement
// ===========================================================================
//
// The bridge lowers a CHECKED index `v[i]` over a receiver decomposed into a data
// pointer `data` + a length `len` into: a bounds `ICmp Ult(i, len)` guarding a
// `CondBr` (the `index out of bounds` `panic_bounds_check` on the out-of-bounds
// edge), then — on the in-bounds edge — an `emit_element_addr(data, i, elem_size)`
// address computation (`data + i*elem_size`, with the `size == 1` `Mul` skip). This
// lane reconstructs the bounds "continue" predicate + the element-address VALUE
// SYMBOLICALLY from the exact trust-ir the bridge EMITTED (the `ICmp`, and the
// `emit_element_addr` Copy/PtrToInt/Copy/[Const,Mul]/Add/IntToPtr), naming the
// receiver's `data`/`len`/`i` (external values the folded slice never defines) by
// their `ValueId`. The SPEC side (`mir_semantics::vec_index_spec`) re-derives the
// SAME trap + address from the Rust definition over the SAME symbolic names. The
// two meet only on those names — so a bridge that DROPS or INVERTS the `i < len`
// check (the real O0 `v[oob]`-reads-silently soundness bug class), scales the
// address by the wrong element size, or computes it off the wrong base folds to a
// genuinely different formula and REFUTES. A shape the fold does not recognise (a
// MISSING bounds check, an unexpected instruction) returns `None` — the statement
// is SKIPPED, never guessed at (sound: less coverage, never a wrong verdict). The
// `unsafe` UNCHECKED variants (`get_unchecked*`) are NEVER captured (the lowering
// gates the capture on `checked`), so they can be neither falsely refuted nor
// falsely refined.
//
// This reuses the `split_at` `Sv`/`sv_*`/`sa_value_name`/`icmp_bool` machinery
// verbatim; the only structural difference is that the fold's OUTPUT is a single
// address VALUE (the i-th element's byte address — the terminal `IntToPtr` of the
// captured slice), not a set of destination stores.

/// The bridge's reconstructed checked index: the bounds "continue" (no-trap)
/// predicate and the emitted element-address value.
pub(crate) struct VecIndexFolded {
    /// The reconstructed bounds "continue" (no-trap) predicate — the emitted
    /// bounds `ICmp`'s comparison over the symbolic `i`/`len`. The bridge branches
    /// to the in-bounds work block when this holds and TRAPS (the `index out of
    /// bounds` panic) otherwise.
    ok: SmtExpr,
    /// The reconstructed i-th element byte address (`data + i*elem_size`) — the
    /// value of the terminal `IntToPtr` of the captured `emit_element_addr` slice.
    elem_addr: SmtExpr,
    /// Symbolic 64-bit inputs the reconstruction references.
    inputs: Vec<(String, u32)>,
}

/// Fold the EMITTED trust-ir of a CHECKED-index lowering (the bounds `ICmp Ult(i,
/// len)` and the `emit_element_addr` Copy/PtrToInt/Copy/[Const,Mul]/Add/IntToPtr
/// address computation) into a [`VecIndexFolded`].
///
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp` — never a re-derivation from the spec — so a
/// wrong emitted formula produces a wrong folded value here and the obligation
/// against the layout-independent spec REFUTES (the anti-tautology guarantee). The
/// element address is the value bound to the FINAL node of the slice (the terminal
/// `IntToPtr`); the captured slice EXCLUDES the trailing `Copy`-to-dest / assign
/// stores / branch, so the last node is exactly the address. Returns `None` (skip
/// the statement, sound) for ANY instruction outside this slice, a MISSING bounds
/// check (`ok` never set), or a terminal value that is not a 64-bit address (e.g. a
/// `Bool` — the ICmp is not the terminal, so the address arithmetic is absent).
pub(crate) fn fold_emitted_vec_index(nodes: &[InstrNode]) -> Option<VecIndexFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut ok: Option<SmtExpr> = None;

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr` /
            // `coerce_to_i64`): propagate the operand value.
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The (single) bounds-check `ICmp` -> the continue predicate. Its result
            // feeds a `CondBr` outside the folded slice; it is bound as a `Bool` so a
            // (malformed) shape flowing an `ICmp` result into arithmetic bails the
            // fold (`sv_bv`/`Cast` reject a `Bool`), never mis-folding it as an
            // external pointer.
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                if ok.is_some() {
                    return None; // more than one comparison is out of shape
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                ok = Some(icmp_bool(*op, l, r));
                bind_sv(&mut env, node, Sv::Bool)?;
            }

            // Anything else is out of the vec-index fold slice.
            _ => return None,
        }
    }

    let ok = ok?; // a MISSING bounds check -> None (fail-closed skip)
    // The element address is the terminal value of the captured slice (the final
    // `IntToPtr` the bridge emits for `emit_element_addr`). A slice whose last node
    // is the `ICmp` (no address arithmetic) yields a `Bool` here -> None (skip).
    let last = nodes.last()?;
    let [addr_result] = last.results.as_slice() else {
        return None;
    };
    let addr_sv = env.get(addr_result).cloned()?;
    let elem_addr = sv_bv(&mut inputs, addr_sv)?;
    Some(VecIndexFolded {
        ok,
        elem_addr,
        inputs,
    })
}

/// Pair the reconstructed bridge checked index (`folded`) with the Rust
/// [`vec_index_spec`] over the SAME symbolic `data`/`len`/`i` names and build the
/// two refinement obligations:
///   * `trap`      — the bridge traps (takes the non-`ok` edge) IFF `i >=u len`;
///   * `elem_addr` — the reconstructed element address equals `data + i*elem_size`.
///
/// `data`/`len`/`i` are the receiver's data-pointer / length / index `ValueId`s
/// (named via [`sa_value_name`], matching the fold); `elem_size` is the element
/// stride in bytes. This lane covers the checked (`index`/`index_mut`) path only —
/// the caller must never queue an `unsafe` `get_unchecked*` (there is no trap to
/// refine against). Always returns `Some` (both obligations are unconditional).
pub(crate) fn vec_index_obligations(
    name: &str,
    folded: &VecIndexFolded,
    data: ValueId,
    len: ValueId,
    i: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: VecIndexSpec = vec_index_spec(
        &sa_value_name(data),
        &sa_value_name(len),
        &sa_value_name(i),
        elem_size,
    );

    // Declare every symbolic name either side references: the fold names
    // `data`/`len`/`i` identically to the spec, so `folded.inputs` normally already
    // covers `spec.inputs`; union them anyway so an emission that referenced a
    // receiver value only on the spec side is still fully declared.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // Trap predicate as a 1-bit BV (matching the bridge's `ICmp`+`CondBr` edge): the
    // bridge traps on the NON-`ok` edge; the spec traps iff `i >=u len`. The two are
    // complementary comparisons — structurally distinct (non-vacuous), equivalent
    // only when the emitted bounds check is exactly `i <u len`.
    let one = SmtExpr::bv_const(1, 1);
    let zero = SmtExpr::bv_const(0, 1);
    let bridge_trap = SmtExpr::ite(folded.ok.clone(), zero.clone(), one.clone());
    let spec_trap = SmtExpr::ite(spec.trap.clone(), one, zero);

    Some(vec![
        split_at_obligation(name, "trap", bridge_trap, spec_trap, inputs),
        split_at_obligation(name, "elem_addr", folded.elem_addr.clone(), spec.elem_addr, inputs),
    ])
}

// ===========================================================================
// `<Vec<T> as Index<Range|RangeFrom|RangeTo>>::index` / `index_mut` range
// SUBSLICE (`&v[a..b]` / `&v[a..]` / `&v[..b]`) VALUE-level refinement
// ===========================================================================
//
// The bridge lowers a checked Vec range subslice over a receiver decomposed into a
// data pointer `data` + a length `len` into: the subslice `{ data + start*elem_size,
// end - start }` written through TWO `InsertField`s (lane 0 = data ptr, lane 1 =
// len) into the destination `{data,len}` slot, then a COMBINED bounds check
// `ok = (start <=u end) AND (end <=u len)` — TWO `ICmp Ule`s combined by a Bool
// `And` — guarding a `CondBr` (the `range end index out of range` panic on the
// out-of-range edge). The endpoints depend on the range form (`a..b`: start=a,
// end=b; `a..`: start=a, end=len; `..b`: start=0-base, end=b), but EVERY form emits
// this SAME shape. This lane reconstructs the combined no-trap predicate + the two
// `{ptr,len}` field VALUES SYMBOLICALLY from the exact trust-ir the bridge EMITTED
// (`emit_element_addr`'s Mul/Add for the pointer, the `Sub` for the length, the two
// `InsertField`s, and the two `ICmp`s + `And`), naming the receiver's
// `data`/`len`/`start`/`end` (external values the folded slice never defines) by
// their `ValueId`. The SPEC side (`mir_semantics::vec_range_subslice_spec`)
// re-derives the SAME subslice from the Rust definition over the SAME symbolic
// names. The two meet only on those names — so a bridge that DROPS a bound
// (fail-closed skip), INVERTS or makes INCOMPLETE (single-comparison) the check,
// scales the pointer by the wrong element size, computes the length off the wrong
// `Sub` direction, or computes the pointer off the wrong base folds to a genuinely
// different formula and REFUTES. A shape the fold does not recognise (a MISSING
// bounds check, an unexpected instruction) returns `None` — the statement is
// SKIPPED, never guessed at (sound: less coverage, never a wrong verdict). The
// `str` range subslice (which adds `is_char_boundary` checks) is a DIFFERENT
// lowering and is never captured on this path.
//
// This reuses the `split_at` `Sv`/`sv_*`/`sa_value_name`/`icmp_bool` machinery; the
// only structural difference is the COMBINED (two-`ICmp` + `And`) predicate — so the
// fold tracks each `ICmp`/`And` boolean's reconstructed predicate and takes the LAST
// boolean produced (the `And`, or a lone `ICmp` for the incomplete-check shape) as
// the `ok` continue predicate.

/// The bridge's reconstructed checked Vec range subslice: the COMBINED bounds
/// "continue" (no-trap) predicate and the emitted `{data,len}` field stores.
pub(crate) struct VecRangeSubsliceFolded {
    /// The reconstructed "continue" (no-trap) predicate — the emitted
    /// `(start <=u end) AND (end <=u len)` combined check (or a lone comparison for
    /// an INCOMPLETE emission). The bridge branches to the subslice's normal target
    /// when this holds and TRAPS (the out-of-range panic) otherwise.
    ok: SmtExpr,
    /// The emitted fat-ptr field stores as `(dest byte offset, lane, value)` — one
    /// per `InsertField` the bridge performed into the destination `{data,len}` slot
    /// (lane 0 = data ptr, lane 1 = len). All share the one destination base.
    stores: Vec<(u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references.
    inputs: Vec<(String, u32)>,
}

impl VecRangeSubsliceFolded {
    /// The value stored into the fat-ptr slot at byte `offset`, lane `lane`.
    fn store_value(&self, offset: u64, lane: u32) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(o, l, _)| *o == offset && *l == lane)
            .map(|(_, _, v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a Vec range-subslice lowering (the
/// `emit_element_addr` Mul/Add for the result pointer, the `Sub` for the result
/// length, the two `InsertField`s that write `{data,len}` into the destination slot,
/// and the two `ICmp Ule`s + Bool `And` combined bounds check) into a
/// [`VecRangeSubsliceFolded`].
///
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`And`/`InsertField` — never a re-derivation
/// from the spec — so a wrong emitted formula produces a wrong folded value here and
/// the obligation against the layout-independent spec REFUTES (the anti-tautology
/// guarantee). Each `ICmp`/`And` boolean's predicate is tracked; the `ok` continue
/// predicate is the LAST boolean produced (the `And`, or a lone `ICmp` for an
/// INCOMPLETE single-comparison emission). Returns `None` (skip the statement, sound)
/// for ANY instruction outside this slice, a MISSING bounds check (no boolean
/// produced), an `And` whose operands are not both reconstructed comparisons, or
/// destination stores that do not all share the one slot base.
pub(crate) fn fold_emitted_vec_range_subslice(nodes: &[InstrNode]) -> Option<VecRangeSubsliceFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp`/`And` result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // The predicate of the most recently produced boolean = the `ok` continue
    // predicate (the `And` in a well-formed emission; a lone `ICmp` if incomplete).
    let mut last_bool: Option<SmtExpr> = None;
    // (dest base, byte offset, lane, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr` /
            // `coerce_to_i64`): propagate the operand value.
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The Bool `And` combining the two bounds comparisons. BOTH operands must
            // be reconstructed comparison predicates (a non-boolean `And` is out of the
            // subslice fold slice). Its result is the combined continue predicate.
            Inst::BinOp {
                op: TrustIrBinOp::And,
                lhs,
                rhs,
                ..
            } => {
                let (Some(l), Some(r)) = (bool_preds.get(lhs).cloned(), bool_preds.get(rhs).cloned())
                else {
                    return None;
                };
                let [result] = node.results.as_slice() else {
                    return None;
                };
                let pred = l.and_expr(r);
                bool_preds.insert(*result, pred.clone());
                last_bool = Some(pred);
                env.insert(*result, Sv::Bool);
            }

            // A bounds-check `ICmp` -> a comparison predicate. Its result feeds the
            // `And` (or the `CondBr` directly, for the incomplete shape) outside the
            // arithmetic; it is bound as a `Bool` so a (malformed) shape flowing an
            // `ICmp` result into arithmetic / a store value bails the fold
            // (`sv_bv`/`Cast` reject a `Bool`), never mis-folding it as an external
            // pointer. Its reconstructed predicate is recorded for the `And`.
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                let pred = icmp_bool(*op, l, r);
                bool_preds.insert(*result, pred.clone());
                last_bool = Some(pred);
                env.insert(*result, Sv::Bool);
            }

            // A fat-ptr field store into the destination `{data,len}` slot. The
            // aggregate operand is `dest_base + const_offset`; the value is a
            // reconstructed 64-bit half field. The `InsertField` result is not read
            // further.
            Inst::InsertField {
                aggregate,
                field,
                value,
                ..
            } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *aggregate) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, *field, val));
            }

            // Anything else is out of the range-subslice fold slice.
            _ => return None,
        }
    }

    let ok = last_bool?; // a MISSING bounds check -> None (fail-closed skip)
    // Every store must target the SAME destination base (the fat-ptr slot).
    let base0 = stores.first()?.0;
    if !stores.iter().all(|(b, ..)| *b == base0) {
        return None;
    }
    let stores = stores.into_iter().map(|(_, o, f, v)| (o, f, v)).collect();
    Some(VecRangeSubsliceFolded { ok, stores, inputs })
}

/// Pair the reconstructed bridge Vec range subslice (`folded`) with the Rust
/// [`vec_range_subslice_spec`] over the SAME symbolic `data`/`len`/`a`/`b` names and
/// build the three refinement obligations:
///   * `trap`       — the bridge traps (takes the non-`ok` edge) IFF
///                    `NOT((start <=u end) AND (end <=u len))`;
///   * `result_ptr` — the value stored at `data_off` lane 0 equals
///                    `data + start*elem_size`;
///   * `result_len` — `data_off` lane 1 equals `end - start`.
///
/// `data_off` is the destination fat-ptr slot's base byte offset (the layout the
/// bridge stored through — `0`, both lanes sharing the one slot base); `form` selects
/// how the endpoints bind (`RangeFrom` anchors `end` to `len`); `data`/`len`/`a`/`b`
/// are the receiver's data-pointer / length / start / end `ValueId`s (named via
/// [`sa_value_name`], matching the fold). Returns `None` when the reconstructed
/// stores do not cover the two fat-ptr lanes (a shape mismatch — fail closed, never
/// a wrong verdict).
#[allow(clippy::too_many_arguments)]
pub(crate) fn vec_range_subslice_obligations(
    name: &str,
    folded: &VecRangeSubsliceFolded,
    form: RangeForm,
    data_off: u64,
    data: ValueId,
    len: ValueId,
    a: ValueId,
    b: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: VecRangeSubsliceSpec = vec_range_subslice_spec(
        form,
        &sa_value_name(data),
        &sa_value_name(len),
        &sa_value_name(a),
        &sa_value_name(b),
        elem_size,
    );

    let result_ptr = folded.store_value(data_off, 0)?;
    let result_len = folded.store_value(data_off, 1)?;

    // Declare every symbolic name either side references: the fold names
    // `data`/`len`/`a`/`b` identically to the spec, so `folded.inputs` normally
    // already covers `spec.inputs`; union them anyway so an emission that referenced
    // a receiver value only on the spec side is still fully declared.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // Trap predicate as a 1-bit BV (matching the bridge's combined-check `CondBr`
    // edge): the bridge traps on the NON-`ok` edge; the spec traps iff
    // `NOT((start <=u end) AND (end <=u len))`. Structurally distinct (non-vacuous),
    // equivalent only when the emitted combined check matches the Rust order+end gate.
    let one = SmtExpr::bv_const(1, 1);
    let zero = SmtExpr::bv_const(0, 1);
    let bridge_trap = SmtExpr::ite(folded.ok.clone(), zero.clone(), one.clone());
    let spec_trap = SmtExpr::ite(spec.trap.clone(), one, zero);

    Some(vec![
        split_at_obligation(name, "trap", bridge_trap, spec_trap, inputs),
        split_at_obligation(name, "result_ptr", result_ptr, spec.result_ptr, inputs),
        split_at_obligation(name, "result_len", result_len, spec.result_len, inputs),
    ])
}

/// The bridge's reconstructed niche-`Option<&T>` first/last accessor: the value the
/// emitted `Select` wrote into the `Option`'s single niche field.
pub(crate) struct OptionRefFolded {
    /// The reconstructed value stored into the niche field — an `ITE` over the
    /// EMITTED emptiness `ICmp` (`then` = the reconstructed element pointer, `else` =
    /// the reconstructed `None` niche value). Its whole content IS the observable
    /// `Option<&T>`.
    niche: SmtExpr,
    /// Symbolic 64-bit inputs the reconstruction references (`data`/`len`).
    inputs: Vec<(String, u32)>,
}

/// Fold the EMITTED trust-ir of a `<[T]>::first`/`last` lowering — the emptiness
/// `ICmp Ne(len, 0)`, the element-address arithmetic (`data` for `first`;
/// `data + (len-1)*size` for `last`), the `None`-niche `Const`+`IntToPtr`, the
/// `Select(cond, elem_ptr, none_ptr)`, and the single `Store` of the chosen value
/// into the `Option<&T>` slot's niche field — into an [`OptionRefFolded`].
///
/// Introduces the `Select -> ITE` fold primitive: the chosen niche value is
/// reconstructed as `ITE(pred, then, else)` where `pred` is the reconstructed
/// predicate of the EMITTED `Select` condition (read from the emitted `ICmp`, so an
/// INVERTED condition — `Some` on an empty slice — folds to the inverted `ITE` and
/// REFUTES against the spec) and `then`/`else` are the reconstructed 64-bit pointer
/// operands (so a NON-NULL `None`, or a `Last` element at the wrong index, folds to
/// a different value and REFUTES). Never re-derives from the spec (the anti-tautology
/// guarantee). Returns `None` (skip the statement, sound) for ANY instruction
/// outside this slice, a `Select` whose condition is not a reconstructed predicate,
/// or a missing/duplicated niche store.
pub(crate) fn fold_emitted_slice_first_last(nodes: &[InstrNode]) -> Option<OptionRefFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp` result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // The value the single niche `Store` wrote (there is exactly one).
    let mut niche: Option<SmtExpr> = None;

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr`/`coerce_to_i64`).
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value (the `None` niche's `IntToPtr(0)` propagates the `0`).
            // A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The emptiness `ICmp Ne(len, 0)` -> a comparison predicate. Bound as a
            // `Bool` so a shape flowing an `ICmp` result into arithmetic / a store
            // value bails the fold (`sv_bv`/`Cast` reject a `Bool`).
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                bool_preds.insert(*result, icmp_bool(*op, l, r));
                env.insert(*result, Sv::Bool);
            }

            // THE NICHE SELECT: `cond ? elem_ptr : none_ptr`. The condition MUST be a
            // reconstructed predicate (a raw non-`ICmp` cond takes the fold out of
            // slice); `then`/`else` are reconstructed 64-bit pointer values. The
            // result is the ITE over the ACTUAL emitted condition + operands.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // WIDTH GATE (the lane-9 width class): a NARROW Select over
                // runtime values TRUNCATES at machine level while the fold
                // models it at 64 bits. The ONE legitimate narrow shape is the
                // Direct-tag pipeline's Select at the layout tag width over the
                // small discriminant CONSTANTS (e.g. the I8 `0`/`1` tags) —
                // width-independent because the constants fit the width and the
                // tag store is separately width-checked. Anything else narrow
                // (or wider than 8 bytes) bails (skip, sound).
                let w = scalar_byte_width(ty)?;
                if w != 8 {
                    if w > 8 {
                        return None;
                    }
                    let shift = w * 8;
                    let fits = |sv: &Sv| matches!(sv, Sv::Int(v) if *v >= 0 && (*v >> shift) == 0);
                    if !(fits(&lookup_sv(&env, *then_val)) && fits(&lookup_sv(&env, *else_val))) {
                        return None;
                    }
                }
                let Some(pred) = bool_preds.get(cond).cloned() else {
                    return None;
                };
                let then_bv = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let else_bv = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, then_bv, else_bv)))?;
            }

            // The single niche `Store` into the `Option<&T>` slot. Capture the chosen
            // value; a SECOND store (an unexpected shape) bails. The destination
            // address is unconstrained here (there is one niche slot) — the store
            // VALUE is the whole observable result.
            Inst::Store { value, .. } => {
                if niche.is_some() {
                    return None;
                }
                niche = Some(sv_bv(&mut inputs, lookup_sv(&env, *value))?);
            }

            // Anything else is out of the first/last fold slice.
            _ => return None,
        }
    }

    let niche = niche?; // a MISSING niche store -> None (fail-closed skip)
    Some(OptionRefFolded { niche, inputs })
}

/// Pair the reconstructed bridge first/last (`folded`) with the Rust
/// [`slice_first_last_spec`] over the SAME symbolic `data`/`len` names and build the
/// single niche-value refinement obligation: the value the bridge stored into the
/// `Option<&T>`'s niche field equals `(len != 0) ? elem_ptr : 0` (with
/// `elem_ptr = data` for `First` / `data + (len-1)*elem_size` for `Last`).
///
/// `data`/`len` are the receiver's data-pointer / length `ValueId`s (named via
/// [`sa_value_name`], matching the fold). Structurally distinct (non-vacuous):
/// equal only when the emitted emptiness test, element index, element scale, and
/// null `None` all match the Rust semantics.
pub(crate) fn slice_first_last_obligations(
    name: &str,
    folded: &OptionRefFolded,
    kind: SliceEndKind,
    data: ValueId,
    len: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: OptionRefSpec =
        slice_first_last_spec(kind, &sa_value_name(data), &sa_value_name(len), elem_size);

    // Declare every symbolic name either side references (the fold names
    // `data`/`len` identically to the spec; union defensively).
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    Some(vec![split_at_obligation(
        name,
        "option_ref",
        folded.niche.clone(),
        spec.niche,
        inputs,
    )])
}

// ===========================================================================
// `<Range<T> as Iterator>::next` STATE-TRANSITION VALUE-level refinement
// ===========================================================================
//
// The FIRST lane with a state transition: the bridge both READS the pre-state
// (`self.start` / `self.end` loads) and WRITES the post-state (the advanced
// `self.start` store) in addition to the `Option<T>` result. This introduces
// the `Inst::Load -> symbolic pre-state` fold primitive: each emitted `Load`
// from a reconstructed `base + const_off` address binds its result to the fresh
// pre-state symbol `ld_value_name(base, off)`, and each emitted `Store` is
// captured as `(base, off, width, reconstructed value)`. The SPEC side
// (`mir_semantics::range_next_spec`) re-derives the tag / payload / new-start
// formulas from the Rust definition over the SAME pre-state symbols. The two
// meet only on those symbols — so a signedness confusion, an advance-when-done,
// a `step != 1`, a swapped `start`/`end` load, or a `payload = new_start`
// (post-increment yield) folds to a genuinely different formula and REFUTES. A
// shape the fold does not recognise (a non-8-byte load, an unexpected
// instruction, a store set that is not EXACTLY the three expected cells)
// returns `None` — the statement is SKIPPED, never guessed at (sound: less
// coverage, never a wrong verdict).

/// The bridge's reconstructed `Range::next`: every emitted typed `Store` (the
/// `self.start` write-back + the `Option<T>` tag and payload stores), each with
/// its reconstructed destination cell and value, plus the pre-state load symbols
/// the reconstruction references.
pub(crate) struct RangeNextFolded {
    /// The emitted typed stores as `(base, byte offset, width, value)` — the
    /// destination cell reconstructed from the emitted address arithmetic, the
    /// value from the emitted dataflow. The obligation builder requires this set
    /// to be EXACTLY the three Range::next cells (state write-back, tag, payload).
    stores: Vec<(ValueId, u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references (the pre-state
    /// `ld_value_name` load symbols; external bases never appear as store values
    /// in this lane's shape, but any referenced one is declared here too).
    inputs: Vec<(String, u32)>,
}

impl RangeNextFolded {
    /// The value stored into the cell at `(base, off)`, if exactly that cell was
    /// written.
    fn store_value(&self, base: ValueId, off: u64) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(b, o, ..)| *b == base && *o == off)
            .map(|(.., v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a `Range::next` lowering (`lower_range_next`) —
/// the `start`/`end` pre-state `Load`s, the `iter_field_addr` address chain for
/// the `end` field, the `ICmp`, the `+1` `Add`, the `new_start` / tag `Select`s,
/// and the three typed `Store`s (state write-back + `Option` tag + payload) —
/// into a [`RangeNextFolded`].
///
/// Introduces the `Inst::Load -> symbolic pre-state` primitive: a `Load` whose
/// address reconstructs to `base + const_off` binds its result to the fresh
/// symbol [`ld_value_name`]`(base, off)` (registered as an input), so every
/// downstream formula is expressed over the ACTUAL loaded pre-state cells — a
/// bridge that loads the wrong field names a different symbol and REFUTES.
/// LANE 13 (narrow elements): 8-byte AND 1/2/4-byte elements are in slice —
/// narrow loads bind the MASKED width-tagged symbol (`ld_value_name_w`), narrow
/// `Add`/`ICmp`/`Select` fold WIDTH-FAITHFULLY (wrap-masked add, sign-extended
/// signed compare, masked-arm select — each modeling trust-ir `interpret.rs`;
/// see the per-arm comments), and everything else keeps its strict 8-byte gate.
/// These narrow relaxations exist ONLY in this fold; every other fold keeps its
/// hard 8-byte gates.
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`Select`/`Load`/`Store` — never a
/// re-derivation from the spec — so a wrong emitted formula produces a wrong
/// folded value here and the obligation against the Rust spec REFUTES (the
/// anti-tautology guarantee). Returns `None` (skip the statement, sound) for ANY
/// instruction outside this slice, a load through an unreconstructed address, or
/// an emission with no store at all.
pub(crate) fn fold_emitted_range_next(nodes: &[InstrNode]) -> Option<RangeNextFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp` result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // Every emitted typed store: (base, byte offset, width, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();
    // LANE 13 (narrow elements): the byte width each in-slice `ValueId`'s folded
    // expression is KNOWN masked to (a narrow load / narrow add / narrow Select
    // result). The width-aware `ICmp`/`Select` arms accept an `Sv::Expr` operand
    // ONLY when it is recorded here at exactly the op's width — an unmasked
    // 64-bit value flowing into a narrow compare would diverge from the machine
    // on the high bits (the lane-9 width class), so it bails instead.
    let mut narrow_w: HashMap<ValueId, u32> = HashMap::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr`/`coerce_to_i64`).
            // Propagates the operand's known-masked width (a `Copy` preserves the
            // value exactly).
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                if let (Some(w), [result]) = (narrow_w.get(operand).copied(), node.results.as_slice())
                {
                    narrow_w.insert(*result, w);
                }
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            // `Add`/`Sub`/`Mul` — WIDTH-DISPATCHED (lane 13): 8-byte arithmetic
            // keeps the exact lane-7 fold (address chains, the 64-bit `+1`);
            // NARROW (1/2/4-byte) arithmetic is WIDTH-FAITHFUL — the machine
            // wraps at the type width (trust-ir `interpret.rs::eval_int_binop`:
            // `BinOp::Add => lhs.raw.wrapping_add(rhs.raw)` then `… & mask`
            // with `mask = int_mask(bits)`), modeled as
            // `bvand(bvadd(l, r), mask(w))` over `w`-masked operands (the
            // result mask makes the wrap exact; operands must vet through
            // `narrow_masked_operand` — masked in-slice values or defensively
            // masked constants — else the fold bails, skip, sound). Any other
            // width is out of slice.
            Inst::BinOp {
                op: op @ (TrustIrBinOp::Add | TrustIrBinOp::Sub | TrustIrBinOp::Mul),
                ty,
                lhs,
                rhs,
                ..
            } => match scalar_byte_width(ty)? {
                8 => {
                    let (a, b) = (lookup_sv(&env, *lhs), lookup_sv(&env, *rhs));
                    let v = match op {
                        TrustIrBinOp::Add => sv_add(&mut inputs, a, b)?,
                        TrustIrBinOp::Sub => sv_sub(&mut inputs, a, b)?,
                        _ => sv_mul(&mut inputs, a, b)?,
                    };
                    bind_sv(&mut env, node, v)?;
                }
                w @ (1 | 2 | 4) => {
                    let l = narrow_masked_operand(&env, &narrow_w, *lhs, w)?;
                    let r = narrow_masked_operand(&env, &narrow_w, *rhs, w)?;
                    let raw = match op {
                        TrustIrBinOp::Add => l.bvadd(r),
                        TrustIrBinOp::Sub => l.bvsub(r),
                        _ => l.bvmul(r),
                    };
                    let masked = raw.bvand(SmtExpr::bv_const(low_bytes_mask(w), 64));
                    let [result] = node.results.as_slice() else {
                        return None;
                    };
                    narrow_w.insert(*result, w);
                    bind_sv(&mut env, node, Sv::Expr(masked))?;
                }
                _ => return None,
            },

            // The `start < end` `ICmp` -> a comparison predicate. Bound as a `Bool`
            // so a shape flowing an `ICmp` result into arithmetic / a store value
            // bails the fold (`sv_bv`/`Cast` reject a `Bool`). WIDTH-DISPATCHED
            // (lane 13): the 8-byte compare keeps the exact lane-7 fold; a NARROW
            // (1/2/4-byte) compare is WIDTH-FAITHFUL via [`icmp_bool_w`] (unsigned
            // = the masked 64-bit compare; signed = sign-extend-then-compare,
            // modeling `interpret.rs::eval_int_icmp`'s `as_signed` decode) over
            // operands vetted `w`-masked by `narrow_masked_operand` (anything
            // else bails — skip, sound).
            Inst::ICmp { op, ty, lhs, rhs, .. } => match scalar_byte_width(ty)? {
                8 => {
                    let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                    let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                    let [result] = node.results.as_slice() else {
                        return None;
                    };
                    bool_preds.insert(*result, icmp_bool(*op, l, r));
                    env.insert(*result, Sv::Bool);
                }
                w @ (1 | 2 | 4) => {
                    let l = narrow_masked_operand(&env, &narrow_w, *lhs, w)?;
                    let r = narrow_masked_operand(&env, &narrow_w, *rhs, w)?;
                    let [result] = node.results.as_slice() else {
                        return None;
                    };
                    bool_preds.insert(*result, icmp_bool_w(*op, w, l, r));
                    env.insert(*result, Sv::Bool);
                }
                _ => return None,
            },

            // A `Select` (`new_start = cond ? advanced : start`; `tag = cond ?
            // some : none`). The condition MUST be a reconstructed predicate (a raw
            // non-`ICmp` cond takes the fold out of slice); `then`/`else` are
            // reconstructed 64-bit values. The result is the ITE over the ACTUAL
            // emitted condition + operands.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // WIDTH GATE (the lane-9 width class): a NARROW Select over
                // runtime values TRUNCATES at machine level while the fold
                // models it at 64 bits. The lane-10 legitimate narrow shape is
                // the Direct-tag pipeline's Select at the layout tag width over
                // the small discriminant CONSTANTS (e.g. the I8 `0`/`1` tags) —
                // width-independent because the constants fit the width and the
                // tag store is separately width-checked (kept EXACTLY, first).
                // LANE-13 RELAXATION (THIS FOLD ONLY): a narrow Select over
                // RUNTIME values is in slice when BOTH arms vet `w`-masked
                // through `narrow_masked_operand` (in-slice masked values or
                // defensively masked constants) — the machine picks one of two
                // already-`w`-byte values, so the ITE over masked operands is
                // width-faithful; the result is recorded masked-at-`w`.
                // Anything else narrow (or wider than 8 bytes) bails (skip,
                // sound).
                let w = scalar_byte_width(ty)?;
                if w != 8 {
                    if w > 8 {
                        return None;
                    }
                    let shift = w * 8;
                    let fits = |sv: &Sv| matches!(sv, Sv::Int(v) if *v >= 0 && (*v >> shift) == 0);
                    if !(fits(&lookup_sv(&env, *then_val)) && fits(&lookup_sv(&env, *else_val))) {
                        // Lane-13 masked-runtime-arms path.
                        let Some(pred) = bool_preds.get(cond).cloned() else {
                            return None;
                        };
                        let t = narrow_masked_operand(&env, &narrow_w, *then_val, w)?;
                        let e = narrow_masked_operand(&env, &narrow_w, *else_val, w)?;
                        let [result] = node.results.as_slice() else {
                            return None;
                        };
                        narrow_w.insert(*result, w);
                        bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, t, e)))?;
                        continue;
                    }
                    // Fitting-constant arms are `w`-masked by definition.
                    if let [result] = node.results.as_slice() {
                        narrow_w.insert(*result, w);
                    }
                }
                let Some(pred) = bool_preds.get(cond).cloned() else {
                    return None;
                };
                let then_bv = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let else_bv = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, then_bv, else_bv)))?;
            }

            // THE PRE-STATE LOAD: a typed `Load` from a reconstructed
            // `base + const_off` cell binds its result to the fresh pre-state
            // symbol. 8-byte loads keep the lane-7 unmasked [`ld_value_name`]
            // binding; NARROW (1/2/4-byte) loads are the lane-11 WIDTH-FAITHFUL
            // primitive — bound to `bvand(var(ld_value_name_w(..), 64),
            // mask(w))`, the machine's "read exactly w bytes" (`interpret.rs`
            // `eval_load` reads `byte_size(ty)` bytes; the decoded value is
            // masked to the type's bits by `InterpretInt::from_raw`) — and
            // recorded masked-at-`w`. Any other width bails (skip, sound).
            //
            // LOAD-AFTER-STORE BAILS (adversarial-review defect 1, CONFIRMED by
            // a solver probe): the pre-state symbol is only valid while the cell
            // is UNWRITTEN in the captured slice. A load appearing after ANY
            // captured store would bind the POST-store runtime value to the
            // PRE-state symbol — e.g. a write-back-then-reload payload emission
            // (the post-increment-yield bug) would discharge Refined. The real
            // emission performs all pre-state loads before any store, so any
            // load-after-store is out of slice.
            Inst::Load { ty, ptr, .. } => {
                if !stores.is_empty() {
                    return None;
                }
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = match width {
                    8 => {
                        let name = ld_value_name(base, off);
                        if !inputs.iter().any(|(n, _)| n == &name) {
                            inputs.push((name.clone(), 64));
                        }
                        Sv::Expr(SmtExpr::var(name, 64))
                    }
                    1 | 2 | 4 => {
                        let name = ld_value_name_w(base, off, width);
                        if !inputs.iter().any(|(n, _)| n == &name) {
                            inputs.push((name.clone(), 64));
                        }
                        let [result] = node.results.as_slice() else {
                            return None;
                        };
                        narrow_w.insert(*result, width);
                        Sv::Expr(
                            SmtExpr::var(name, 64)
                                .bvand(SmtExpr::bv_const(low_bytes_mask(width), 64)),
                        )
                    }
                    _ => return None,
                };
                bind_sv(&mut env, node, val)?;
            }

            // A typed `Store` to a reconstructed `base + const_off` cell: capture
            // the destination cell + the reconstructed value. The obligation
            // builder enforces the exact three-cell store set.
            Inst::Store { ty, ptr, value, .. } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, width, val));
            }

            // Anything else is out of the Range::next fold slice.
            _ => return None,
        }
    }

    if stores.is_empty() {
        return None; // no store at all -> out of slice (fail-closed skip)
    }
    Some(RangeNextFolded { stores, inputs })
}

/// Pair the reconstructed bridge `Range::next` (`folded`) with the Rust
/// [`range_next_spec`] over the SAME pre-state load symbols and build the three
/// refinement obligations:
///   * `state_new_start` — the value written back to `(self_base, 0)` equals
///                         `ITE(start < end, start + 1, start)`;
///   * `option_tag`      — `(dest_base, tag_off)` equals
///                         `ITE(start < end, some_discr, none_discr)`;
///   * `option_payload`  — `(dest_base, payload_off)` equals `start` (the
///                         PRE-state start — the yielded value).
///
/// `start`/`end` are the pre-state symbols [`ld_value_name`]`(self_base, 0)` /
/// `(self_base, elem_size)` (matching the fold's `Load` binding, so a swapped or
/// wrong-field load names a different symbol and REFUTES).
///
/// SOUNDNESS SHAPE CHECK (mandatory): the folded store set must be EXACTLY
/// `{ (self_base, 0, elem_size), (dest_base, tag_off, tag_width),
/// (dest_base, payload_off, elem_size) }` — one store each AT THE EXPECTED
/// WIDTH (lane 13: the write-back/payload width is the ELEMENT width, 8 for
/// the landed 64-bit lane and 1/2/4 for narrow elements, whose obligations are
/// then compared AT WIDTH), no extras, no duplicates, and the three cells
/// pairwise DISTINCT (narrow branch: byte-range DISJOINT per base). An EXTRA
/// self-store could clobber the `end` field (invalidating the pre-state symbols
/// the formulas are expressed over); a MISSING one hides a dropped state
/// write-back; a NARROW write-back/payload store (adversarial-review defect 2)
/// would truncate the 64-bit value at runtime while folding to the full-width
/// formula (e.g. an I32 write-back wraps `start` at 2^32 -> an infinite
/// iterator) — so the write-back and payload must be exactly 8 bytes, and the
/// tag store exactly the LAYOUT-designated tag width (`tag_width`, 1 byte for
/// `Option<i64>`'s i8 tag — a 1-byte tag store is the correct full-tag write,
/// NOT a truncation). NON-DISTINCT expected cells (defect 4) would let one
/// store satisfy two expectations and leave a third store unvalidated. Any
/// deviation returns `None` (skip, sound — the drain's shape-miss trace makes
/// it visible).
#[allow(clippy::too_many_arguments)]
pub(crate) fn range_next_obligations(
    name: &str,
    folded: &RangeNextFolded,
    signed: bool,
    self_base: ValueId,
    dest_base: ValueId,
    elem_size: u64,
    tag_off: u64,
    tag_width: u32,
    payload_off: u64,
    some_discr: u64,
    none_discr: u64,
) -> Option<Vec<ProofObligation>> {
    // WIDTH DISPATCH (lane 13): `elem_size == 8` keeps the EXACT lane-7 spec
    // pairing and obligations (unmasked, over `ld_value_name` symbols — zero
    // behavior change); `elem_size` in `{1, 2, 4}` pairs against the
    // WIDTH-FAITHFUL [`range_next_spec_w`] over the MASKED width-tagged
    // pre-state symbols (`ld_value_name_w`, matching the narrow-load fold
    // binding) and compares every store obligation AT ITS STORE WIDTH
    // (`bvand` both sides with the width mask — the machine writes exactly
    // that many bytes). Any other element size is out of shape (skip, sound).
    let w = match elem_size {
        8 => 8u32,
        1 | 2 | 4 => elem_size as u32,
        _ => return None,
    };
    let spec: RangeNextSpec = if w == 8 {
        range_next_spec(
            signed,
            &ld_value_name(self_base, 0),
            &ld_value_name(self_base, elem_size),
            some_discr,
            none_discr,
        )
    } else {
        range_next_spec_w(
            signed,
            w,
            &ld_value_name_w(self_base, 0, w),
            &ld_value_name_w(self_base, elem_size, w),
            some_discr,
            none_discr,
            tag_width,
        )
    };

    // The mandatory shape check (see the doc comment): exactly one store per
    // expected (cell, width), exactly three stores overall, cells pairwise
    // distinct — the write-back and payload stores at the ELEMENT width (an
    // 8-byte write-back of a 4-byte element would clobber `end`; a narrow
    // write-back of an 8-byte element would truncate — both are width lies).
    let expected = [
        (self_base, 0u64, w),
        (dest_base, tag_off, tag_width),
        (dest_base, payload_off, w),
    ];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            if expected[i].0 == expected[j].0 && expected[i].1 == expected[j].1 {
                return None; // degenerate layout: expected cells not distinct
            }
            // NARROW-branch hardening (no landed-behavior change at 8 bytes):
            // same-base expected cells must have pairwise DISJOINT byte ranges
            // — with sub-8-byte cells, offset-distinctness alone would admit a
            // partially-overlapping pair, making the per-cell obligations
            // order-sensitive.
            if w != 8 && expected[i].0 == expected[j].0 {
                let (a0, a1) = (expected[i].1, expected[i].1 + u64::from(expected[i].2));
                let (b0, b1) = (expected[j].1, expected[j].1 + u64::from(expected[j].2));
                if a0 < b1 && b0 < a1 {
                    return None; // overlapping expected cells
                }
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, ew) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == ew)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let new_start = folded.store_value(self_base, 0)?;
    let tag = folded.store_value(dest_base, tag_off)?;
    let payload = folded.store_value(dest_base, payload_off)?;

    // Declare every symbolic name either side references (the fold binds the
    // pre-state loads to the same `ld_value_name`/`ld_value_name_w` symbols
    // the spec is built over; union defensively).
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    if w == 8 {
        return Some(vec![
            split_at_obligation(name, "state_new_start", new_start, spec.new_start, inputs),
            split_at_obligation(name, "option_tag", tag, spec.tag, inputs),
            split_at_obligation(name, "option_payload", payload, spec.payload, inputs),
        ]);
    }
    // NARROW obligations: compare each store AT ITS WIDTH — the machine writes
    // exactly `w` (resp. `tag_width`) bytes, so only those bytes are
    // observable (`interpret.rs::eval_store` writes `byte_size(ty)` bytes).
    // Masking BOTH sides makes an emission that computes wide but stores
    // narrow (e.g. a 64-bit add whose result feeds a 4-byte store) compare
    // exactly as the machine behaves.
    let m = SmtExpr::bv_const(low_bytes_mask(w), 64);
    let tag_m = if tag_width >= 8 {
        None
    } else {
        Some(SmtExpr::bv_const(low_bytes_mask(tag_width), 64))
    };
    let (tag_l, tag_r) = match tag_m {
        Some(tm) => (tag.bvand(tm.clone()), spec.tag.bvand(tm)),
        None => (tag, spec.tag),
    };
    Some(vec![
        split_at_obligation(
            name,
            "state_new_start",
            new_start.bvand(m.clone()),
            spec.new_start.bvand(m.clone()),
            inputs,
        ),
        split_at_obligation(name, "option_tag", tag_l, tag_r, inputs),
        split_at_obligation(
            name,
            "option_payload",
            payload.bvand(m.clone()),
            spec.payload.bvand(m),
            inputs,
        ),
    ])
}

// ===========================================================================
// `<slice::Iter<T> as Iterator>::next` STATE-TRANSITION VALUE-level refinement
// (lane 9 — the `for x in slice` workhorse)
// ===========================================================================
//
// Composes the two landed primitives: the lane-7 `Inst::Load -> symbolic
// pre-state` fold (each emitted `Load` from a reconstructed `base + const_off`
// cell binds its result to the fresh symbol `ld_value_name(base, off)`) and the
// lane-5 niche-`Option<&T>` Select shape (the `store_option_some_value`
// Reference arm: `None` is the null niche, the yielded reference chosen by a
// `Select` over the exhaustion `ICmp`). The SPEC side
// (`mir_semantics::slice_iter_next_spec`) re-derives the new-ptr / niche
// formulas from the Rust definition over the SAME pre-state symbols. The two
// meet only on those symbols — so an advance-when-done, a wrong stride, a
// post-increment yield (`Some(&*(ptr + size))`, an off-by-one-ELEMENT read), a
// non-null `None`, an end-clobbering write-back, or an `Eq`-for-`Ne` inverted
// exhaustion test folds to a genuinely different formula and REFUTES. A shape
// the fold does not recognise (a non-8-byte load, an unexpected instruction, a
// store set that is not EXACTLY the two expected cells) returns `None` — the
// statement is SKIPPED, never guessed at (sound: less coverage, never a wrong
// verdict).

/// The bridge's reconstructed slice `Iter::next`: every emitted typed `Store`
/// (the `self.ptr` write-back + the niche-`Option<&T>` store), each with its
/// reconstructed destination cell and value, plus the pre-state load symbols
/// the reconstruction references.
pub(crate) struct SliceIterNextFolded {
    /// The emitted typed stores as `(base, byte offset, width, value)` — the
    /// destination cell reconstructed from the emitted address arithmetic, the
    /// value from the emitted dataflow. The obligation builder requires this set
    /// to be EXACTLY the two slice-Iter::next cells (state write-back, niche).
    stores: Vec<(ValueId, u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references (the pre-state
    /// `ld_value_name` load symbols; external bases never appear as store values
    /// in this lane's shape, but any referenced one is declared here too).
    inputs: Vec<(String, u32)>,
}

impl SliceIterNextFolded {
    /// The value stored into the cell at `(base, off)`, if exactly that cell was
    /// written.
    fn store_value(&self, base: ValueId, off: u64) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(b, o, ..)| *b == base && *o == off)
            .map(|(.., v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a slice `Iter::next` lowering
/// (`lower_slice_iter_next`) — the `ptr`/`end` pre-state `Load`s, the
/// `iter_field_addr` address chain for the `end` field, the `emit_ptr_to_int`
/// `Copy`+`PtrToInt` pairs, the `ICmp Ne`, the `emit_element_addr` advance, the
/// `new_ptr` / niche `Select`s, and the two typed `Store`s (state write-back +
/// `Option<&T>` niche) — into a [`SliceIterNextFolded`].
///
/// The lane-7 `Inst::Load -> symbolic pre-state` primitive: a `Load` whose
/// address reconstructs to `base + const_off` binds its result to the fresh
/// symbol [`ld_value_name`]`(base, off)` (registered as an input), so every
/// downstream formula is expressed over the ACTUAL loaded pre-state cells — a
/// bridge that loads the wrong field names a different symbol and REFUTES.
/// 8-byte (pointer) loads only in this lane: a `Load` of any other scalar width
/// bails. Reconstructs each value from the REAL emitted `Const`/`Copy`/
/// `PtrToInt`/`IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`Select`/`Load`/`Store` —
/// never a re-derivation from the spec — so a wrong emitted formula produces a
/// wrong folded value here and the obligation against the Rust spec REFUTES
/// (the anti-tautology guarantee). Returns `None` (skip the statement, sound)
/// for ANY instruction outside this slice, a load through an unreconstructed
/// address, or an emission with no store at all.
pub(crate) fn fold_emitted_slice_iter_next(nodes: &[InstrNode]) -> Option<SliceIterNextFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp` result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // Every emitted typed store: (base, byte offset, width, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr`/`coerce_to_i64`).
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value (the `None` niche's `IntToPtr(0)` propagates the
            // `0`). A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The `ptr != end` `ICmp` -> a comparison predicate. Bound as a `Bool`
            // so a shape flowing an `ICmp` result into arithmetic / a store value
            // bails the fold (`sv_bv`/`Cast` reject a `Bool`).
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                bool_preds.insert(*result, icmp_bool(*op, l, r));
                env.insert(*result, Sv::Bool);
            }

            // A `Select` (`new_ptr = cond ? advanced : ptr`; `niche = cond ?
            // ptr : none`). The condition MUST be a reconstructed predicate (a raw
            // non-`ICmp` cond takes the fold out of slice); `then`/`else` are
            // reconstructed 64-bit values. The result is the ITE over the ACTUAL
            // emitted condition + operands.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // WIDTH GATE (the lane-9 width class): a NARROW Select over
                // runtime values TRUNCATES at machine level while the fold
                // models it at 64 bits. The ONE legitimate narrow shape is the
                // Direct-tag pipeline's Select at the layout tag width over the
                // small discriminant CONSTANTS (e.g. the I8 `0`/`1` tags) —
                // width-independent because the constants fit the width and the
                // tag store is separately width-checked. Anything else narrow
                // (or wider than 8 bytes) bails (skip, sound).
                let w = scalar_byte_width(ty)?;
                if w != 8 {
                    if w > 8 {
                        return None;
                    }
                    let shift = w * 8;
                    let fits = |sv: &Sv| matches!(sv, Sv::Int(v) if *v >= 0 && (*v >> shift) == 0);
                    if !(fits(&lookup_sv(&env, *then_val)) && fits(&lookup_sv(&env, *else_val))) {
                        return None;
                    }
                }
                let Some(pred) = bool_preds.get(cond).cloned() else {
                    return None;
                };
                let then_bv = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let else_bv = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, then_bv, else_bv)))?;
            }

            // THE PRE-STATE LOAD: a typed `Load` from a reconstructed
            // `base + const_off` cell binds its result to the fresh pre-state
            // symbol `ld_value_name(base, off)`. 8-byte pointer cells only in
            // this lane — any other width bails (skip, sound).
            //
            // LOAD-AFTER-STORE BAILS (the lane-7 adversarial-review defect 1,
            // CONFIRMED by a solver probe there — non-negotiable here): the
            // pre-state symbol is only valid while the cell is UNWRITTEN in the
            // captured slice. A load appearing after ANY captured store would
            // bind the POST-store runtime value to the PRE-state symbol — e.g. a
            // write-back-then-reload niche emission (the post-increment-yield
            // bug via reload) would discharge Refined. The real emission
            // performs all pre-state loads before any store, so any
            // load-after-store is out of slice.
            Inst::Load { ty, ptr, .. } => {
                if !stores.is_empty() {
                    return None;
                }
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                if width != 8 {
                    return None;
                }
                let name = ld_value_name(base, off);
                if !inputs.iter().any(|(n, _)| n == &name) {
                    inputs.push((name.clone(), 64));
                }
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::var(name, 64)))?;
            }

            // A typed `Store` to a reconstructed `base + const_off` cell: capture
            // the destination cell + the reconstructed value. The obligation
            // builder enforces the exact two-cell store set.
            Inst::Store { ty, ptr, value, .. } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, width, val));
            }

            // Anything else is out of the slice-Iter::next fold slice.
            _ => return None,
        }
    }

    if stores.is_empty() {
        return None; // no store at all -> out of slice (fail-closed skip)
    }
    Some(SliceIterNextFolded { stores, inputs })
}

/// Pair the reconstructed bridge slice `Iter::next` (`folded`) with the Rust
/// [`slice_iter_next_spec`] over the SAME pre-state load symbols and build the
/// two refinement obligations:
///   * `state_new_ptr` — the value written back to `(self_base, 0)` equals
///                       `ITE(ptr != end, ptr + elem_size, ptr)`;
///   * `option_niche`  — `(dest_base, tag_off)` equals `ITE(ptr != end, ptr, 0)`
///                       (the yielded reference IS the PRE-advance `ptr`; `None`
///                       is the null niche).
///
/// `ptr`/`end` are the pre-state symbols [`ld_value_name`]`(self_base, 0)` /
/// `(self_base, end_off)` (matching the fold's `Load` binding, so a swapped or
/// wrong-field load names a different symbol and REFUTES).
///
/// SOUNDNESS SHAPE CHECK (mandatory, lane-7-hardened): the folded store set
/// must be EXACTLY `{ (self_base, 0, 8), (dest_base, tag_off, 8) }` — one store
/// each AT 8 BYTES, no extras, no duplicates, and the two cells pairwise
/// DISTINCT. An EXTRA self-store could clobber the `end` field (invalidating
/// the pre-state symbols the formulas are expressed over); a MISSING one hides
/// a dropped state write-back; a NARROW write-back/niche store (the lane-7
/// adversarial-review defect 2) would truncate the 64-bit pointer at runtime
/// while folding to the full-width formula (e.g. an I32 write-back wraps the
/// cursor at 2^32 -> a wild pointer). NON-DISTINCT expected cells (defect 4)
/// would let one store satisfy two expectations and leave another store
/// unvalidated. Any deviation returns `None` (skip, sound — the drain's
/// shape-miss trace makes it visible).
pub(crate) fn slice_iter_next_obligations(
    name: &str,
    folded: &SliceIterNextFolded,
    self_base: ValueId,
    dest_base: ValueId,
    elem_size: u64,
    end_off: u64,
    tag_off: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: SliceIterNextSpec = slice_iter_next_spec(
        &ld_value_name(self_base, 0),
        &ld_value_name(self_base, end_off),
        elem_size,
    );

    // The mandatory shape check (see the doc comment): exactly one store per
    // expected (cell, width), exactly two stores overall, cells pairwise
    // distinct.
    let expected = [(self_base, 0u64, 8u32), (dest_base, tag_off, 8u32)];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            if expected[i].0 == expected[j].0 && expected[i].1 == expected[j].1 {
                return None; // degenerate layout: expected cells not distinct
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, w) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == w)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let new_ptr = folded.store_value(self_base, 0)?;
    let niche = folded.store_value(dest_base, tag_off)?;

    // Declare every symbolic name either side references (the fold binds the
    // pre-state loads to the same `ld_value_name` symbols the spec is built
    // over; union defensively).
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    Some(vec![
        split_at_obligation(name, "state_new_ptr", new_ptr, spec.new_ptr, inputs),
        split_at_obligation(name, "option_niche", niche, spec.niche, inputs),
    ])
}

// ===========================================================================
// `<StepBy<Range<i64>> as Iterator>::next` STATE-TRANSITION VALUE-level
// refinement (lane 11 — the WIDTH-FAITHFUL lane)
// ===========================================================================
//
// Extends the lane-7/9 skeleton with WIDTH-FAITHFUL fold primitives: every
// value stays a 64-bit `SmtExpr` but narrow (1/2/4-byte) loads and the
// `ZExt`/`Trunc` casts around them are folded as EXPLICIT masking formulas
// that match trust-ir's `interpret.rs` semantics (a `w`-byte load reads
// exactly `w` bytes — `eval_load` reads `byte_size(ty)` bytes and the decoded
// `InterpretInt.raw` is masked to `bits`; `Trunc`/`ZExt` produce
// `from_raw(dst_bits, …, raw)` = `raw & mask(dst_bits)`; `ZExt` of an
// already-masked value zero-fills):
//   * NARROW LOAD (w in {1,2,4}): the result is bound to
//     `bvand(var(ld_value_name_w(base, off, w), 64), mask(w))` — the pre-state
//     symbol is declared 64-bit but the VALUE is its low `w` bytes. 8-byte
//     loads keep the existing unmasked `ld_value_name` binding (lanes 7/9
//     backward compatible).
//   * `ZExt(w -> 64)`: the operand is already masked by construction (the
//     masked narrow load / masked `Trunc` / fitting narrow-Select constants
//     are the only narrow producers) => IDENTITY propagation for a folded
//     expression; a CONSTANT is masked to `w`; an EXTERNAL (undefined) operand
//     is masked to `w` (its full 64-bit symbol would otherwise leak unmasked).
//   * `Trunc(64 -> w)`: `bvand(v, mask(w))`.
//   * `SExt` is NOT in slice (the real i64 emission never emits it: the
//     `first_take` extend is documented unsigned => `ZExt`, and the i64
//     element extends are identity => nothing is emitted) — it bails.
// The lane-10 hard 8-byte Cast gate RELAXES here ONLY into these faithful
// formulas; every OTHER fold arm keeps its hard 8-byte gates
// (`PtrToInt`/`IntToPtr`, `Add`/`Sub`/`Mul`, `ICmp` all stay 8-byte-only), and
// the Bool `And` arm (the `no_overflow AND in_range` guard) is lane-4's: both
// operands must be reconstructed comparison predicates.
//
// The SPEC side (`mir_semantics::step_by_next_spec`) re-derives the
// new-start / new-first-take / tag / payload formulas from the Rust definition
// over the SAME pre-state symbols. The two meet only on those symbols — so
// swapped countdown arms, a dropped overflow guard, an advance-when-done, a
// `first_take` never cleared / cleared unconditionally, a post-increment
// payload, swapped tag arms, a wrong-cell store, or a narrow-store WIDTH LIE
// (the `first_take` store must be exactly 1 byte) folds to a genuinely
// different formula / fails the shape check and is REFUTED / skipped. A shape
// the fold does not recognise returns `None` — the statement is SKIPPED,
// never guessed at (sound: less coverage, never a wrong verdict).

/// The bridge's reconstructed `StepBy<Range<i64>>::next`: every emitted typed
/// `Store` (the `range.start` write-back, the 1-byte `first_take` write-back,
/// and the `Option<i64>` tag and payload stores), each with its reconstructed
/// destination cell and value, plus the pre-state load symbols the
/// reconstruction references.
pub(crate) struct StepByNextFolded {
    /// The emitted typed stores as `(base, byte offset, width, value)` — the
    /// destination cell reconstructed from the emitted address arithmetic, the
    /// value from the emitted dataflow. The obligation builder requires this
    /// set to be EXACTLY the four StepBy::next cells (cursor write-back,
    /// 1-byte `first_take` write-back, tag, payload).
    stores: Vec<(ValueId, u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references (the pre-state
    /// `ld_value_name` / `ld_value_name_w` load symbols; any referenced
    /// external base is declared here too).
    inputs: Vec<(String, u32)>,
}

impl StepByNextFolded {
    /// The value stored into the cell at `(base, off)`, if exactly that cell
    /// was written.
    fn store_value(&self, base: ValueId, off: u64) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(b, o, ..)| *b == base && *o == off)
            .map(|(.., v)| v.clone())
    }
}

/// The low-`width`-bytes mask as a 64-bit constant (`width` in `{1, 2, 4}`).
fn low_bytes_mask(width: u32) -> u64 {
    (1u64 << (8 * width)) - 1
}

/// Fold the EMITTED trust-ir of a `StepBy::next` lowering
/// (`lower_step_by_next` — ONE fold serves all three shapes: the v1
/// SIGNED-Range-i64 std-layout path, the lane-12 PACKED-UNSIGNED Range path
/// (whose `And`/`LShr`/`Shl`/`Or` prelude folds through the 8-byte arithmetic
/// arms), and the lane-12 STD-LAYOUT SLICE-source path (whose
/// `emit_element_addr` stride arithmetic and niche-`Option<&T>` dest reuse the
/// lane-9 patterns)). For the v1 shape that is — the `Const 0`,
/// the `iter_field_addr` chains, the `step_minus_one` (I64) + `first_take`
/// (I8, NARROW) pre-state `Load`s, the `ZExt(I8 -> I64)`, the `first_take != 0`
/// `ICmp Ne`, the countdown `Select`, the `start`/`end` (I64) pre-state
/// `Load`s, the `y = start + countdown` `Add`, the `Sge`/`Slt` guards and
/// their Bool `And`, the `y + 1` `Add`, the `new_start` / `new_ft` / tag
/// `Select`s, the `Trunc(I64 -> I8)`, and the four typed `Store`s — into a
/// [`StepByNextFolded`].
///
/// WIDTH-FAITHFUL primitives (see the section comment): a NARROW load binds
/// `bvand(var, mask(w))` over the width-tagged symbol [`ld_value_name_w`];
/// `ZExt` propagates the already-masked operand; `Trunc` masks. Everything
/// else keeps the lane-7/9/10 hard 8-byte gates, the load-after-store bail,
/// and the Bool-`And`-over-predicates arm. Reconstructs each value from the
/// REAL emitted ops — never a re-derivation from the spec — so a wrong
/// emitted formula produces a wrong folded value here and the obligation
/// against the Rust spec REFUTES (the anti-tautology guarantee). Returns
/// `None` (skip the statement, sound) for ANY instruction outside this slice,
/// a load through an unreconstructed address, or an emission with no store at
/// all.
pub(crate) fn fold_emitted_step_by_next(nodes: &[InstrNode]) -> Option<StepByNextFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp` / Bool-`And`
    // result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // Every emitted typed store: (base, byte offset, width, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr`/`coerce_to_i64`).
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value. A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // while the fold would propagate the full 64-bit symbol. The
                // lane-11 width-faithful relaxation applies ONLY to ZExt/Trunc
                // below; pointer casts stay 8-byte-only (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            // WIDTH-FAITHFUL `ZExt(w -> 64)` (the `first_take` widening): the
            // operand's folded value is ALREADY masked to `w` bytes (the masked
            // narrow-load / masked-`Trunc` / fitting-narrow-Select constructs
            // are the only narrow producers in this slice), and the machine's
            // `ZExt` zero-fills (`interpret.rs`: `from_raw` keeps the
            // already-masked `raw`) => IDENTITY propagation. A CONSTANT is
            // masked to `w` (the machine value of a `w`-wide constant is its
            // low `w` bytes); an EXTERNAL (undefined) operand is masked to `w`
            // (its 64-bit symbol must not leak unmasked). A boolean bails.
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty,
                dst_ty,
                operand,
            } => {
                let sw = scalar_byte_width(src_ty)?;
                if !matches!(sw, 1 | 2 | 4) || scalar_byte_width(dst_ty) != Some(8) {
                    return None; // only the narrow->64 widening is in slice
                }
                let mask = low_bytes_mask(sw);
                let val = match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    Sv::Int(v) => Sv::Int(v & i128::from(mask)),
                    Sv::Expr(e) => Sv::Expr(e),
                    v @ Sv::Ptr { .. } => {
                        let e = sv_bv(&mut inputs, v)?;
                        Sv::Expr(e.bvand(SmtExpr::bv_const(mask, 64)))
                    }
                };
                bind_sv(&mut env, node, val)?;
            }

            // WIDTH-FAITHFUL `Trunc(64 -> w)` (the `first_take` narrowing
            // before its 1-byte store): `bvand(v, mask(w))`, matching the
            // machine (`interpret.rs`: `from_raw(dst_bits, …, raw)` masks to
            // the destination width). A boolean bails (`sv_bv` rejects it); a
            // CONSTANT is masked as a constant.
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty,
                dst_ty,
                operand,
            } => {
                let dw = scalar_byte_width(dst_ty)?;
                if scalar_byte_width(src_ty) != Some(8) || !matches!(dw, 1 | 2 | 4) {
                    return None; // only the 64->narrow truncation is in slice
                }
                let mask = low_bytes_mask(dw);
                let val = match lookup_sv(&env, *operand) {
                    Sv::Int(v) => Sv::Int(v & i128::from(mask)),
                    v => {
                        let e = sv_bv(&mut inputs, v)?;
                        Sv::Expr(e.bvand(SmtExpr::bv_const(mask, 64)))
                    }
                };
                bind_sv(&mut env, node, val)?;
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // `And` — TYPE-DISPATCHED (lane 12): the Bool `And` combining the
            // `no_overflow` / `in_range` guards (lane-4's arm — BOTH operands
            // must be reconstructed comparison predicates), OR the 8-byte
            // ARITHMETIC `bvand` of the packed prelude
            // (`countdown = state & 0xFFFF_FFFF`). The machine's `And` is a
            // plain bitwise AND masked to the type width (`interpreter.rs`
            // `BinOp::And`: `normalize_int(a & b, ty, width)`), so at 8 bytes
            // `bvand` is exact. A narrow (non-Bool, non-8-byte) `And`
            // truncates at machine level — out of slice (the lane-9 width
            // class). An `ICmp` result flowing into the arithmetic arm bails
            // (`sv_bv` rejects a `Bool`).
            Inst::BinOp {
                op: TrustIrBinOp::And,
                ty,
                lhs,
                rhs,
                ..
            } => match ty {
                TrustIrTy::Bool => {
                    let (Some(l), Some(r)) =
                        (bool_preds.get(lhs).cloned(), bool_preds.get(rhs).cloned())
                    else {
                        return None;
                    };
                    let [result] = node.results.as_slice() else {
                        return None;
                    };
                    bool_preds.insert(*result, l.and_expr(r));
                    env.insert(*result, Sv::Bool);
                }
                _ if scalar_byte_width(ty) == Some(8) => {
                    let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                    let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                    bind_sv(&mut env, node, Sv::Expr(l.bvand(r)))?;
                }
                _ => return None,
            },

            // `Or` — the packed prelude's `new_state_yield = reset_hi | reset`
            // (lane 12). 8-byte-gated arithmetic `bvor`, exactly like the
            // arithmetic `And` above (`interpreter.rs` `BinOp::Or`:
            // `normalize_int(a | b, ty, width)` — a plain bitwise OR at the
            // type width). A Bool `Or` never appears in these slices — out of
            // slice (skip, sound).
            Inst::BinOp {
                op: TrustIrBinOp::Or,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow bitwise ops truncate (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, Sv::Expr(l.bvor(r)))?;
            }

            // `Shl` / `LShr` — the packed prelude's `reset = state >> 32` /
            // `reset_hi = reset << 32` (lane 12). 8-byte-gated, and the shift
            // AMOUNT must be a reconstructed CONSTANT IN RANGE `0..64`: the
            // machine makes an out-of-range amount UB
            // (`interpret.rs::shift_amount`: `rhs.raw >= bits` is an
            // interpreter ERROR, not a mod-width wrap), so ANY model of an
            // out-of-range constant would certify UB IR as defined — bail
            // instead (skip, sound — never a divergent model; the emitted
            // amount is always the constant 32). A RUNTIME shift amount is
            // likewise out of slice. For in-range constants `bvshl`/`bvlshr`
            // are exact. `LShr` is the LOGICAL shift (`interpret.rs`
            // `BinOp::LShr` shifts the raw unsigned bits, zero-filling) ==
            // `bvlshr`; no `AShr` arm is needed — `lower_step_by_next` never
            // emits one (it falls to `_ => None`).
            Inst::BinOp {
                op: op @ (TrustIrBinOp::Shl | TrustIrBinOp::LShr),
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow shifts truncate (the lane-9 width class)
                }
                let Sv::Int(amt) = lookup_sv(&env, *rhs) else {
                    return None; // runtime shift amount: out of slice
                };
                // In-range constants ONLY: `interpret.rs::shift_amount` makes
                // `amount >= 64` (incl. any negative raw) UB — modeling it
                // (mod-64 or otherwise) would certify UB IR as defined.
                let amt = u64::try_from(amt).ok().filter(|a| *a < 64)?;
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let amt_bv = SmtExpr::bv_const(amt, 64);
                let v = match op {
                    TrustIrBinOp::Shl => l.bvshl(amt_bv),
                    _ => l.bvlshr(amt_bv),
                };
                bind_sv(&mut env, node, Sv::Expr(v))?;
            }

            // The `first_take != 0` / `y >= start` / `y < end` `ICmp`s -> comparison
            // predicates. Bound as `Bool` so a shape flowing an `ICmp` result into
            // arithmetic / a store value bails the fold (`sv_bv`/`Cast` reject a
            // `Bool`). The emission does ALL comparisons at I64 — narrow compares
            // stay out of slice (the lane-10 hard gate).
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                bool_preds.insert(*result, icmp_bool(*op, l, r));
                env.insert(*result, Sv::Bool);
            }

            // A `Select` (`countdown`, `new_start`, `new_ft`, or the tag). The
            // condition MUST be a reconstructed predicate; `then`/`else` are
            // reconstructed 64-bit values. The result is the ITE over the ACTUAL
            // emitted condition + operands.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // WIDTH GATE (the lane-9 width class): a NARROW Select over
                // runtime values TRUNCATES at machine level while the fold
                // models it at 64 bits. The ONE legitimate narrow shape is the
                // Direct-tag pipeline's Select at the layout tag width over the
                // small discriminant CONSTANTS (the I8 `0`/`1` tags) —
                // width-independent because the constants fit the width and the
                // tag store is separately width-checked. Anything else narrow
                // (or wider than 8 bytes) bails (skip, sound).
                let w = scalar_byte_width(ty)?;
                if w != 8 {
                    if w > 8 {
                        return None;
                    }
                    let shift = w * 8;
                    let fits = |sv: &Sv| matches!(sv, Sv::Int(v) if *v >= 0 && (*v >> shift) == 0);
                    if !(fits(&lookup_sv(&env, *then_val)) && fits(&lookup_sv(&env, *else_val))) {
                        return None;
                    }
                }
                let Some(pred) = bool_preds.get(cond).cloned() else {
                    return None;
                };
                let then_bv = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let else_bv = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, then_bv, else_bv)))?;
            }

            // THE PRE-STATE LOAD: a typed `Load` from a reconstructed
            // `base + const_off` cell binds its result to a fresh pre-state
            // symbol. 8-byte loads keep the lane-7 unmasked [`ld_value_name`]
            // binding; NARROW (1/2/4-byte) loads are the lane-11 WIDTH-FAITHFUL
            // primitive — bound to `bvand(var(ld_value_name_w(..), 64),
            // mask(w))`, the machine's "read exactly w bytes" (`interpret.rs`
            // `eval_load` reads `byte_size(ty)` bytes; the decoded value is
            // masked to the type's bits). Any other width bails (skip, sound).
            //
            // LOAD-AFTER-STORE BAILS (the lane-7 adversarial-review defect 1,
            // CONFIRMED by a solver probe there — non-negotiable here): the
            // pre-state symbol is only valid while the cell is UNWRITTEN in the
            // captured slice. A load appearing after ANY captured store would
            // bind the POST-store runtime value to the PRE-state symbol — e.g.
            // a write-back-then-reload payload emission (the
            // post-increment-yield bug via reload) would discharge Refined. The
            // real emission performs all pre-state loads before any store, so
            // any load-after-store is out of slice.
            Inst::Load { ty, ptr, .. } => {
                if !stores.is_empty() {
                    return None;
                }
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = match width {
                    8 => {
                        let name = ld_value_name(base, off);
                        if !inputs.iter().any(|(n, _)| n == &name) {
                            inputs.push((name.clone(), 64));
                        }
                        Sv::Expr(SmtExpr::var(name, 64))
                    }
                    1 | 2 | 4 => {
                        let name = ld_value_name_w(base, off, width);
                        if !inputs.iter().any(|(n, _)| n == &name) {
                            inputs.push((name.clone(), 64));
                        }
                        Sv::Expr(
                            SmtExpr::var(name, 64)
                                .bvand(SmtExpr::bv_const(low_bytes_mask(width), 64)),
                        )
                    }
                    _ => return None,
                };
                bind_sv(&mut env, node, val)?;
            }

            // A typed `Store` to a reconstructed `base + const_off` cell: capture
            // the destination cell + the reconstructed value AND THE WIDTH. The
            // obligation builder enforces the exact four-cell store set with
            // per-cell widths (the `first_take` store must be exactly 1 byte).
            Inst::Store { ty, ptr, value, .. } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, width, val));
            }

            // Anything else is out of the StepBy::next fold slice.
            _ => return None,
        }
    }

    if stores.is_empty() {
        return None; // no store at all -> out of slice (fail-closed skip)
    }
    Some(StepByNextFolded { stores, inputs })
}

/// Pair the reconstructed bridge `StepBy<Range<i64>>::next` (`folded`) with the
/// Rust [`step_by_next_spec`] over the SAME pre-state load symbols and build
/// the four refinement obligations:
///   * `state_new_start` — the value written back to `(self_base, src_off)`
///                         equals `ITE(cond, y + 1, start)`;
///   * `state_new_ft`    — the LOW BYTE of the value written to
///                         `(self_base, ft_off)` equals the low byte of
///                         `ITE(cond, 0, ft)` (the store is 1 byte wide — the
///                         obligation compares `bvand(v, 0xff)` on BOTH sides);
///   * `option_tag`      — `(dest_base, tag_off)` equals
///                         `ITE(cond, some_discr, none_discr)`;
///   * `option_payload`  — `(dest_base, payload_off)` equals `y` (the yielded
///                         element).
///
/// `sm`/`ft_raw`/`start`/`end` are the pre-state symbols
/// [`ld_value_name`]`(self_base, sm_off)` /
/// [`ld_value_name_w`]`(self_base, ft_off, 1)` /
/// [`ld_value_name`]`(self_base, src_off)` / `(self_base, src_off + 8)`
/// (matching the fold's `Load` bindings, so a swapped or wrong-field load
/// names a different symbol and REFUTES).
///
/// SOUNDNESS SHAPE CHECK (mandatory, lane-7-hardened + per-cell WIDTHS): the
/// folded store set must be EXACTLY `{ (self_base, src_off, 8),
/// (self_base, ft_off, 1), (dest_base, tag_off, tag_width),
/// (dest_base, payload_off, 8) }` — one store each AT THE EXPECTED WIDTH, no
/// extras, no duplicates, and the four cells' BYTE RANGES pairwise DISJOINT
/// (per same base — strictly stronger than offset-distinctness: a
/// partially-overlapping pair would make the per-cell obligations
/// order-sensitive). An EXTRA self-store could clobber the `end`/`sm` cells
/// (invalidating the pre-state symbols); a MISSING one hides a dropped state
/// write-back; a WIDTH LIE (an 8-byte `first_take` store — clobbering 7
/// neighbouring bytes — or a narrow cursor/payload store truncating the
/// value) fails the width-exact check. Any deviation returns `None` (skip,
/// sound — the drain's shape-miss trace makes it visible).
#[allow(clippy::too_many_arguments)]
pub(crate) fn step_by_next_obligations(
    name: &str,
    folded: &StepByNextFolded,
    self_base: ValueId,
    dest_base: ValueId,
    sm_off: u64,
    ft_off: u64,
    src_off: u64,
    tag_off: u64,
    tag_width: u32,
    payload_off: u64,
    some_discr: u64,
    none_discr: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: StepByNextSpec = step_by_next_spec(
        &ld_value_name(self_base, sm_off),
        &ld_value_name_w(self_base, ft_off, 1),
        &ld_value_name(self_base, src_off),
        &ld_value_name(self_base, src_off + 8),
        some_discr,
        none_discr,
        tag_width,
    );

    // The mandatory shape check (see the doc comment): exactly one store per
    // expected (cell, width), exactly four stores overall, same-base cells'
    // byte ranges pairwise disjoint.
    let expected = [
        (self_base, src_off, 8u32),
        (self_base, ft_off, 1u32),
        (dest_base, tag_off, tag_width),
        (dest_base, payload_off, 8u32),
    ];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            let (bi, oi, wi) = expected[i];
            let (bj, oj, wj) = expected[j];
            if bi == bj && oi < oj.checked_add(u64::from(wj))? && oj < oi.checked_add(u64::from(wi))?
            {
                return None; // degenerate layout: expected cells overlap
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, w) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == w)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let new_start = folded.store_value(self_base, src_off)?;
    let new_ft = folded.store_value(self_base, ft_off)?;
    let tag = folded.store_value(dest_base, tag_off)?;
    let payload = folded.store_value(dest_base, payload_off)?;

    // Declare every symbolic name either side references (the fold binds the
    // pre-state loads to the same `ld_value_name`/`ld_value_name_w` symbols
    // the spec is built over; union defensively).
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // The 1-byte `first_take` obligation compares LOW BYTES on both sides (the
    // store writes exactly 1 byte; higher bytes of the 64-bit formulas are not
    // observable). `spec.new_ft` is already masked; mask both explicitly.
    let byte_mask = SmtExpr::bv_const(0xff, 64);
    let new_ft_low = new_ft.bvand(byte_mask.clone());
    let spec_new_ft_low = spec.new_ft.bvand(byte_mask);

    Some(vec![
        split_at_obligation(name, "state_new_start", new_start, spec.new_start, inputs),
        split_at_obligation(name, "state_new_ft", new_ft_low, spec_new_ft_low, inputs),
        split_at_obligation(name, "option_tag", tag, spec.tag, inputs),
        split_at_obligation(name, "option_payload", payload, spec.payload, inputs),
    ])
}

/// Pair the reconstructed bridge PACKED-UNSIGNED `StepBy<Range<u64|usize>>::next`
/// (`folded` — the SAME [`fold_emitted_step_by_next`] serves all three StepBy
/// shapes) with the Rust [`step_by_next_packed_spec`] over the SAME pre-state
/// load symbols and build the four refinement obligations:
///   * `state_new_start` — the value written back to `(self_base, src_off)`
///                         equals `ITE(cond, y + 1, start)`;
///   * `state_new_state` — the value written back to `(self_base, sm_off)` (the
///                         ONE packed I64 word — there is NO `first_take` cell
///                         on this path) equals
///                         `ITE(cond, (reset << 32) | reset, state)`;
///   * `option_tag`      — `(dest_base, tag_off)` equals
///                         `ITE(cond, some_discr, none_discr)`;
///   * `option_payload`  — `(dest_base, payload_off)` equals `y`.
///
/// `state`/`start`/`end` are the pre-state symbols
/// [`ld_value_name`]`(self_base, sm_off)` / `(self_base, src_off)` /
/// `(self_base, src_off + 8)` (matching the fold's `Load` bindings, so a
/// swapped or wrong-field load names a different symbol and REFUTES).
///
/// SOUNDNESS SHAPE CHECK (mandatory — the lane-11 discipline, per-cell WIDTHS):
/// the folded store set must be EXACTLY `{ (self_base, src_off, 8),
/// (self_base, sm_off, 8), (dest_base, tag_off, tag_width),
/// (dest_base, payload_off, 8) }` — one store each AT THE EXPECTED WIDTH, no
/// extras, no duplicates, and the cells' BYTE RANGES pairwise DISJOINT per
/// base. A MISSING state store hides a dropped write-back; an EXTRA one could
/// clobber the `end` cell; a WIDTH LIE (a narrow packed-state store truncating
/// the high `k-1` half) fails the width-exact check. Any deviation returns
/// `None` (skip, sound — the drain's shape-miss trace makes it visible).
#[allow(clippy::too_many_arguments)]
pub(crate) fn step_by_next_packed_obligations(
    name: &str,
    folded: &StepByNextFolded,
    self_base: ValueId,
    dest_base: ValueId,
    sm_off: u64,
    src_off: u64,
    tag_off: u64,
    tag_width: u32,
    payload_off: u64,
    some_discr: u64,
    none_discr: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: StepByNextPackedSpec = step_by_next_packed_spec(
        &ld_value_name(self_base, sm_off),
        &ld_value_name(self_base, src_off),
        &ld_value_name(self_base, src_off + 8),
        some_discr,
        none_discr,
        tag_width,
    );

    // The mandatory shape check: exactly one store per expected (cell, width),
    // exactly four stores overall, same-base cells' byte ranges pairwise
    // disjoint.
    let expected = [
        (self_base, src_off, 8u32),
        (self_base, sm_off, 8u32),
        (dest_base, tag_off, tag_width),
        (dest_base, payload_off, 8u32),
    ];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            let (bi, oi, wi) = expected[i];
            let (bj, oj, wj) = expected[j];
            if bi == bj && oi < oj.checked_add(u64::from(wj))? && oj < oi.checked_add(u64::from(wi))?
            {
                return None; // degenerate layout: expected cells overlap
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, w) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == w)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let new_start = folded.store_value(self_base, src_off)?;
    let new_state = folded.store_value(self_base, sm_off)?;
    let tag = folded.store_value(dest_base, tag_off)?;
    let payload = folded.store_value(dest_base, payload_off)?;

    // Declare every symbolic name either side references.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    Some(vec![
        split_at_obligation(name, "state_new_start", new_start, spec.new_start, inputs),
        split_at_obligation(name, "state_new_state", new_state, spec.new_state, inputs),
        split_at_obligation(name, "option_tag", tag, spec.tag, inputs),
        split_at_obligation(name, "option_payload", payload, spec.payload, inputs),
    ])
}

/// Pair the reconstructed bridge SLICE-source `StepBy<slice::Iter<T>>::next`
/// (`folded` — the SAME [`fold_emitted_step_by_next`] serves all three StepBy
/// shapes) with the Rust [`step_by_next_slice_spec`] over the SAME pre-state
/// load symbols and build the three refinement obligations:
///   * `state_new_ptr` — the value written back to `(self_base, src_off)`
///                       equals `ITE(cond, y_ptr + elem_size, ptr)`;
///   * `state_new_ft`  — the LOW BYTE of the value written to
///                       `(self_base, ft_off)` equals the low byte of
///                       `ITE(cond, 0, ft)` (the store is 1 byte wide — the
///                       obligation compares `bvand(v, 0xff)` on BOTH sides);
///   * `option_niche`  — `(dest_base, tag_off)` (the `Option<&T>`'s single
///                       niche cell) equals `ITE(cond, y_ptr, 0)` — the
///                       PRE-advance element pointer for `Some`, the null 0
///                       for `None`.
///
/// `sm`/`ft_raw`/`ptr`/`end` are the pre-state symbols
/// [`ld_value_name`]`(self_base, sm_off)` /
/// [`ld_value_name_w`]`(self_base, ft_off, 1)` /
/// [`ld_value_name`]`(self_base, src_off)` / `(self_base, src_off + 8)`
/// (matching the fold's `Load` bindings, so a swapped or wrong-field load
/// names a different symbol and REFUTES).
///
/// SOUNDNESS SHAPE CHECK (mandatory — the lane-11 discipline, per-cell WIDTHS):
/// the folded store set must be EXACTLY `{ (self_base, src_off, 8),
/// (self_base, ft_off, 1), (dest_base, tag_off, 8) }` — one store each AT THE
/// EXPECTED WIDTH, no extras, no duplicates, and the same-base cells' BYTE
/// RANGES pairwise DISJOINT. An EXTRA self-store could clobber the `end`/`sm`
/// cells; a MISSING one hides a dropped write-back; a WIDTH LIE (an 8-byte
/// `first_take` store clobbering 7 neighbouring bytes, or a narrow
/// cursor/niche store truncating the pointer) fails the width-exact check.
/// Any deviation returns `None` (skip, sound).
#[allow(clippy::too_many_arguments)]
pub(crate) fn step_by_next_slice_obligations(
    name: &str,
    folded: &StepByNextFolded,
    self_base: ValueId,
    dest_base: ValueId,
    sm_off: u64,
    ft_off: u64,
    src_off: u64,
    elem_size: u64,
    tag_off: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: StepByNextSliceSpec = step_by_next_slice_spec(
        &ld_value_name(self_base, sm_off),
        &ld_value_name_w(self_base, ft_off, 1),
        &ld_value_name(self_base, src_off),
        &ld_value_name(self_base, src_off + 8),
        elem_size,
    );

    // The mandatory shape check: exactly one store per expected (cell, width),
    // exactly three stores overall, same-base cells' byte ranges pairwise
    // disjoint.
    let expected = [
        (self_base, src_off, 8u32),
        (self_base, ft_off, 1u32),
        (dest_base, tag_off, 8u32),
    ];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            let (bi, oi, wi) = expected[i];
            let (bj, oj, wj) = expected[j];
            if bi == bj && oi < oj.checked_add(u64::from(wj))? && oj < oi.checked_add(u64::from(wi))?
            {
                return None; // degenerate layout: expected cells overlap
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, w) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == w)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let new_ptr = folded.store_value(self_base, src_off)?;
    let new_ft = folded.store_value(self_base, ft_off)?;
    let niche = folded.store_value(dest_base, tag_off)?;

    // Declare every symbolic name either side references.
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    // The 1-byte `first_take` obligation compares LOW BYTES on both sides
    // (exactly the v1 discipline).
    let byte_mask = SmtExpr::bv_const(0xff, 64);
    let new_ft_low = new_ft.bvand(byte_mask.clone());
    let spec_new_ft_low = spec.new_ft.bvand(byte_mask);

    Some(vec![
        split_at_obligation(name, "state_new_ptr", new_ptr, spec.new_ptr, inputs),
        split_at_obligation(name, "state_new_ft", new_ft_low, spec_new_ft_low, inputs),
        split_at_obligation(name, "option_niche", niche, spec.niche, inputs),
    ])
}

// ===========================================================================
// `<[T]>::split_first` / `split_last` niche-`Option<(&T, &[T])>` VALUE-level
// refinement (lane 6)
// ===========================================================================
//
// Three written 8-byte cells (the `&T` head pointer, the tail's data pointer,
// the tail length) — reconstructed from the emitted `ICmp`/`Sub`/address
// arithmetic/`Select`/`Store`s. Pure address arithmetic over the OUTSIDE
// `data`/`len` values: there is NO `Load` in this lowering, so the fold has NO
// `Load` arm at all (an `Inst::Load` falls to `_ => return None` — lane-7
// hardening: a load can never silently bind a stale symbol here). THE NICHE
// KEYSTONE: which pointer cell must carry the `ITE(len != 0, ptr, 0)`
// discriminant formula is designated by the LAYOUT (`niche_at_f0`, passed from
// the capture site) — NEVER inferred from where the emitted `Select` flowed —
// so a DROPPED `Select` (the raw pointer stored unconditionally into the niche
// cell; an empty slice would decode `Some`) folds that cell to the raw pointer
// while the spec has the ITE and REFUTES.

/// The bridge's reconstructed `split_first`/`split_last`: every emitted typed
/// `Store` (the niche-`Select` cell + the other pointer cell + the tail-length
/// cell), each with its reconstructed destination cell and value, plus the
/// symbolic inputs the reconstruction references.
pub(crate) struct SplitEndsFolded {
    /// The emitted typed stores as `(base, byte offset, width, value)` — the
    /// destination cell reconstructed from the emitted address arithmetic, the
    /// value from the emitted dataflow. The obligation builder requires this set
    /// to be EXACTLY the three split cells (`f0`, `f1`, `f1+8`).
    stores: Vec<(ValueId, u64, u32, SmtExpr)>,
    /// Symbolic 64-bit inputs the reconstruction references (`data`/`len` and
    /// any external base a folded value names).
    inputs: Vec<(String, u32)>,
}

impl SplitEndsFolded {
    /// The value stored into the cell at `(base, off)`, if exactly that cell was
    /// written.
    fn store_value(&self, base: ValueId, off: u64) -> Option<SmtExpr> {
        self.stores
            .iter()
            .find(|(b, o, ..)| *b == base && *o == off)
            .map(|(.., v)| v.clone())
    }
}

/// Fold the EMITTED trust-ir of a `<[T]>::split_first`/`split_last` lowering
/// (`lower_slice_split_first_last`) — the emptiness `ICmp Ne(len, 0)`, the
/// `tail_len = Sub(len, 1)`, the kind-dependent `emit_element_addr` arithmetic,
/// the `store_option_some_value` `RefAndSlice` arm's `None`-niche
/// `Const`+`IntToPtr`, the niche `Select`, and the three typed `Store`s — into a
/// [`SplitEndsFolded`].
///
/// Reconstructs each value from the REAL emitted `Const`/`Copy`/`PtrToInt`/
/// `IntToPtr`/`Add`/`Sub`/`Mul`/`ICmp`/`Select`/`Store` — never a re-derivation
/// from the spec — so a wrong emitted formula produces a wrong folded value here
/// and the obligation against the Rust spec REFUTES (the anti-tautology
/// guarantee). This lowering performs NO loads, so there is NO `Load` arm: an
/// `Inst::Load` in the captured slice falls to `_ => return None` (skip, sound).
/// Returns `None` for ANY instruction outside this slice, a `Select` whose
/// condition is not a reconstructed predicate, a store through an
/// unreconstructed address, or an emission with no store at all.
pub(crate) fn fold_emitted_split_ends(nodes: &[InstrNode]) -> Option<SplitEndsFolded> {
    let mut env: HashMap<ValueId, Sv> = HashMap::new();
    let mut inputs: Vec<(String, u32)> = Vec::new();
    // Reconstructed predicate of each boolean `ValueId` (an `ICmp` result).
    let mut bool_preds: HashMap<ValueId, SmtExpr> = HashMap::new();
    // Every emitted typed store: (base, byte offset, width, value).
    let mut stores: Vec<(ValueId, u64, u32, SmtExpr)> = Vec::new();

    for node in nodes {
        match &node.inst {
            Inst::Const {
                value: Constant::Int(v),
                ..
            } => bind_sv(&mut env, node, Sv::Int(*v))?,

            // A pointer/int reinterpreting move (`coerce_to_plain_ptr`/`coerce_to_i64`).
            Inst::Copy { operand, .. } => {
                let val = lookup_sv(&env, *operand);
                bind_sv(&mut env, node, val)?;
            }

            // `PtrToInt` / `IntToPtr`: the int image of a pointer (and back) is the
            // SAME 64-bit value (the `None` niche's `IntToPtr(0)` propagates the `0`).
            // A boolean may never flow here.
            Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr,
                src_ty,
                dst_ty,
                operand,
            } => {
                // WIDTH GATE (lane-9 adversarial finding — the cross-lane width
                // class): a NARROW PtrToInt/IntToPtr TRUNCATES at machine level
                // (the interpreter masks the address to dst_bits) while the fold
                // would propagate the full 64-bit symbol — e.g. an I8 exhaustion
                // compare wraps mod 256 yet folds structurally equal to the spec
                // (a solver-CONFIRMED false-Refined). Only 8-byte casts are in
                // slice; anything narrower bails (skip, sound).
                if scalar_byte_width(src_ty) != Some(8) || scalar_byte_width(dst_ty) != Some(8) {
                    return None;
                }
                match lookup_sv(&env, *operand) {
                    Sv::Bool => return None,
                    v => bind_sv(&mut env, node, v)?,
                }
            }

            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_add(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_sub(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }
            Inst::BinOp {
                op: TrustIrBinOp::Mul,
                ty,
                lhs,
                rhs,
                ..
            } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow arithmetic truncates (the lane-9 width class)
                }
                let v = sv_mul(&mut inputs, lookup_sv(&env, *lhs), lookup_sv(&env, *rhs))?;
                bind_sv(&mut env, node, v)?;
            }

            // The emptiness `ICmp Ne(len, 0)` -> a comparison predicate. Bound as a
            // `Bool` so a shape flowing an `ICmp` result into arithmetic / a store
            // value bails the fold (`sv_bv`/`Cast` reject a `Bool`).
            Inst::ICmp { op, ty, lhs, rhs, .. } => {
                if scalar_byte_width(ty) != Some(8) {
                    return None; // narrow compare truncates (the lane-9 width class)
                }
                let l = sv_bv(&mut inputs, lookup_sv(&env, *lhs))?;
                let r = sv_bv(&mut inputs, lookup_sv(&env, *rhs))?;
                let [result] = node.results.as_slice() else {
                    return None;
                };
                bool_preds.insert(*result, icmp_bool(*op, l, r));
                env.insert(*result, Sv::Bool);
            }

            // THE NICHE SELECT: `cond ? ptr : none_ptr`. The condition MUST be a
            // reconstructed predicate (a raw non-`ICmp` cond takes the fold out of
            // slice); `then`/`else` are reconstructed 64-bit pointer values. The
            // result is the ITE over the ACTUAL emitted condition + operands.
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // WIDTH GATE (the lane-9 width class): a NARROW Select over
                // runtime values TRUNCATES at machine level while the fold
                // models it at 64 bits. The ONE legitimate narrow shape is the
                // Direct-tag pipeline's Select at the layout tag width over the
                // small discriminant CONSTANTS (e.g. the I8 `0`/`1` tags) —
                // width-independent because the constants fit the width and the
                // tag store is separately width-checked. Anything else narrow
                // (or wider than 8 bytes) bails (skip, sound).
                let w = scalar_byte_width(ty)?;
                if w != 8 {
                    if w > 8 {
                        return None;
                    }
                    let shift = w * 8;
                    let fits = |sv: &Sv| matches!(sv, Sv::Int(v) if *v >= 0 && (*v >> shift) == 0);
                    if !(fits(&lookup_sv(&env, *then_val)) && fits(&lookup_sv(&env, *else_val))) {
                        return None;
                    }
                }
                let Some(pred) = bool_preds.get(cond).cloned() else {
                    return None;
                };
                let then_bv = sv_bv(&mut inputs, lookup_sv(&env, *then_val))?;
                let else_bv = sv_bv(&mut inputs, lookup_sv(&env, *else_val))?;
                bind_sv(&mut env, node, Sv::Expr(SmtExpr::ite(pred, then_bv, else_bv)))?;
            }

            // A typed `Store` to a reconstructed `base + const_off` cell: capture
            // the destination cell + the reconstructed value. The obligation
            // builder enforces the exact three-cell store set.
            Inst::Store { ty, ptr, value, .. } => {
                let Sv::Ptr { base, off } = lookup_sv(&env, *ptr) else {
                    return None;
                };
                let off = u64::try_from(off).ok()?;
                let width = scalar_byte_width(ty)?;
                let val = sv_bv(&mut inputs, lookup_sv(&env, *value))?;
                stores.push((base, off, width, val));
            }

            // Anything else — including `Inst::Load`, which this loadless lowering
            // never emits (lane-7 hardening: no Load arm at all) — is out of the
            // split_first/split_last fold slice.
            _ => return None,
        }
    }

    if stores.is_empty() {
        return None; // no store at all -> out of slice (fail-closed skip)
    }
    Some(SplitEndsFolded { stores, inputs })
}

/// Pair the reconstructed bridge `split_first`/`split_last` (`folded`) with the
/// Rust [`split_first_last_spec`] over the SAME symbolic `data`/`len` names and
/// build the three refinement obligations:
///   * `split_f0`       — `(dest_base, f0)` equals the spec's `&T` head-pointer
///                        cell (the `ITE(len != 0, first_ptr, 0)` when the
///                        layout put the niche at `f0`, else the raw pointer);
///   * `split_f1`       — `(dest_base, f1)` equals the spec's tail data-pointer
///                        cell (the ITE when the niche is at `f1`, else raw);
///   * `split_tail_len` — `(dest_base, f1+8)` equals `len - 1` (wrapping).
///
/// `data`/`len` are the receiver's data-pointer / length `ValueId`s (named via
/// [`sa_value_name`], matching the fold). `niche_at_f0` is the LAYOUT-designated
/// niche position (the keystone — see [`SplitEndsSpec`]): it selects which spec
/// cell carries the ITE, so a dropped/misplaced emitted `Select` REFUTES.
///
/// SOUNDNESS SHAPE CHECK (lane-7-hardened, mandatory): the folded store set must
/// be EXACTLY `{ (dest_base, f0, 8), (dest_base, f1, 8), (dest_base, f1+8, 8) }`
/// — one store each AT WIDTH 8 (a NARROW store would truncate the pointer/length
/// at runtime while folding to the full-width formula), no extras, no
/// duplicates, and the three cells pairwise DISTINCT (non-distinct expected
/// cells would let one store satisfy two expectations and leave a third store
/// unvalidated). Any deviation returns `None` (skip, sound — the drain's
/// shape-miss trace makes it visible).
#[allow(clippy::too_many_arguments)]
pub(crate) fn split_ends_obligations(
    name: &str,
    folded: &SplitEndsFolded,
    kind: SliceEndKind,
    niche_at_f0: bool,
    dest_base: ValueId,
    f0: u64,
    f1: u64,
    data: ValueId,
    len: ValueId,
    elem_size: u64,
) -> Option<Vec<ProofObligation>> {
    let spec: SplitEndsSpec = split_first_last_spec(
        kind,
        niche_at_f0,
        &sa_value_name(data),
        &sa_value_name(len),
        elem_size,
    );

    // The mandatory shape check (see the doc comment): exactly one store per
    // expected (cell, width), exactly three stores overall, cells pairwise
    // distinct.
    let expected = [
        (dest_base, f0, 8u32),
        (dest_base, f1, 8u32),
        (dest_base, f1 + 8, 8u32),
    ];
    for i in 0..expected.len() {
        for j in (i + 1)..expected.len() {
            if expected[i].0 == expected[j].0 && expected[i].1 == expected[j].1 {
                return None; // degenerate layout: expected cells not distinct
            }
        }
    }
    if folded.stores.len() != expected.len() {
        return None;
    }
    for (b, o, w) in expected {
        let hits = folded
            .stores
            .iter()
            .filter(|(sb, so, sw, _)| *sb == b && *so == o && *sw == w)
            .count();
        if hits != 1 {
            return None;
        }
    }
    let f0_val = folded.store_value(dest_base, f0)?;
    let f1_val = folded.store_value(dest_base, f1)?;
    let tail_len_val = folded.store_value(dest_base, f1 + 8)?;

    // Declare every symbolic name either side references (the fold names
    // `data`/`len` identically to the spec; union defensively).
    let mut inputs = folded.inputs.clone();
    for si in &spec.inputs {
        if !inputs.iter().any(|(nm, _)| nm == &si.0) {
            inputs.push(si.clone());
        }
    }
    let inputs = &inputs;

    Some(vec![
        split_at_obligation(name, "split_f0", f0_val, spec.f0, inputs),
        split_at_obligation(name, "split_f1", f1_val, spec.f1, inputs),
        split_at_obligation(name, "split_tail_len", tail_len_val, spec.tail_len, inputs),
    ])
}

// ===========================================================================
// Unit tests: the IMPL fold is LOAD-BEARING (the anti-tautology keystone).
//
// Each test HAND-BUILDS the exact emitted shape the bridge produces for a
// fixed-offset field access (`emit_i64_const` + `emit_element_addr` +
// `emit_typed_load`), folds it, and discharges the reconstructed bridge ops
// against a layout-style SPEC sequence through `check_memory_sequence`. The
// CORRECT offset must NOT refute; a WRONG offset / SWAPPED base MUST refute.
// ===========================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_verify::ay_bridge::AYConfig;
    use trust_cg_verify::mir_semantics::{check_memory_sequence, MemCheckConfig, RefinementOutcome};

    // The slot base pointer (an external value the per-statement slice never
    // defines), and the fresh SSA values the emitted address arithmetic mints.
    const SLOT: ValueId = ValueId::new(7);
    const V_OFF: ValueId = ValueId::new(20);
    const V_BASEPTR: ValueId = ValueId::new(21);
    const V_BASEINT: ValueId = ValueId::new(22);
    const V_IDX64: ValueId = ValueId::new(23);
    const V_STRIDE: ValueId = ValueId::new(24);
    const V_OFFV: ValueId = ValueId::new(25);
    const V_ADDRINT: ValueId = ValueId::new(26);
    const V_ADDR: ValueId = ValueId::new(27);
    const V_LOADED: ValueId = ValueId::new(28);

    fn node(inst: Inst, result: ValueId) -> InstrNode {
        InstrNode::new(inst).with_result(result)
    }

    /// True while clean's Alethe reconstruction cannot yet verify ay v0.9.0's
    /// and_pos-bridged strict surface (ay c74bc60bd1), or while a v0.9.0-era
    /// authority answers the obligation VERDICTLESS under its strict
    /// self-certification envelope: the cross-check lane fail-closes to
    /// Inconclusive instead of confirming the refutation. When clean's
    /// checker learns the surface — and once the installed authority upgrades
    /// to ay main build.7534+, which publishes `unsat` with the hole
    /// disclosure again (accepted by the established `incomplete AY proof
    /// certificate:` shape) — this stops matching and every guarded test
    /// resumes its original refutation/discharge assertion automatically —
    /// the exemption cannot rot.
    fn alethe_crosscheck_gap(outcome: &RefinementOutcome) -> bool {
        match outcome {
            RefinementOutcome::Inconclusive { reason } => {
                // Shape 1: solver present, but clean's Alethe reconstruction
                // cannot yet verify ay v0.9.0's and_pos-bridged strict
                // surface (ay c74bc60bd1).
                (reason.contains("AY reported UNSAT but")
                    && reason
                        .contains("rejected or could not fully verify the exact Alethe proof"))
                // Shape 2: no solver discoverable at all (the release gate's
                // anonymous clone) — the lane refuses to credit a wide
                // obligation on a statistical verdict, the same "verified
                // MODULO solver" doctrine run_public_release_checks.sh
                // applies to its other solver lanes.
                    || (reason.contains("no solver available")
                        && reason.contains("statistical"))
                // Shape 3: v0.9.0-era authorities answer the larger blasts
                // VERDICTLESS — AY COMPUTES UNSAT and then its mandatory
                // strict self-certification declines the proof on a resource
                // envelope (RUP expansion work limit), publishing
                // `unknown (:reason-unknown (incomplete self-check-rejected))`
                // instead of the verdict (ay 3cb091d23c). Matched ONLY on the
                // reason-bearing transcript, NEVER on a bare
                // "unknown: unknown": the resident ay server discards stderr
                // and truncates this shape, and a bare unknown must keep
                // failing. Delegates the canonical phrase to
                // `trust_cg_verify::gap_classify` so this copy cannot drift.
                    || reason.strip_prefix("unknown: ").is_some_and(|s| {
                        s.contains("(:reason-unknown")
                            && trust_cg_verify::gap_classify::ay_reason_is_self_check_rejection(s)
                    })
            }
            _ => false,
        }
    }

    /// The skip notice printed by every test parked behind
    /// `alethe_crosscheck_gap`.
    const ALETHE_GAP_SKIP_NOTICE: &str =
        "skipping assertion: clean's Alethe reconstruction cannot yet verify ay \
         v0.9.0's and_pos-bridged strict surface (ay c74bc60bd1); the \
         cross-check lane fail-closed to Inconclusive";

    /// The EXACT instruction sequence the bridge emits for a fixed-offset scalar
    /// field load `*(I64*)(slot + offset)` (mirrors `memory_place_address` ->
    /// `emit_i64_const` + `emit_element_addr` + `emit_typed_load`).
    fn emitted_field_load(offset: i128) -> Vec<InstrNode> {
        vec![
            // idx = const offset
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(offset),
                },
                V_OFF,
            ),
            // base_ptr = Copy(slot)            (coerce_to_plain_ptr)
            node(
                Inst::Copy {
                    ty: TrustIrTy::Ptr,
                    operand: SLOT,
                },
                V_BASEPTR,
            ),
            // base_int = PtrToInt(base_ptr)
            node(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: TrustIrTy::Ptr,
                    dst_ty: TrustIrTy::I64,
                    operand: V_BASEPTR,
                },
                V_BASEINT,
            ),
            // idx64 = Copy(idx)                (coerce_to_i64)
            node(
                Inst::Copy {
                    ty: TrustIrTy::I64,
                    operand: V_OFF,
                },
                V_IDX64,
            ),
            // stride = const 1
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(1),
                },
                V_STRIDE,
            ),
            // offv = idx64 * stride
            node(
                Inst::BinOp {
                    op: TrustIrBinOp::Mul,
                    ty: TrustIrTy::I64,
                    lhs: V_IDX64,
                    rhs: V_STRIDE,
                },
                V_OFFV,
            ),
            // addr_int = base_int + offv
            node(
                Inst::BinOp {
                    op: TrustIrBinOp::Add,
                    ty: TrustIrTy::I64,
                    lhs: V_BASEINT,
                    rhs: V_OFFV,
                },
                V_ADDRINT,
            ),
            // addr = IntToPtr(addr_int)
            node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: TrustIrTy::I64,
                    dst_ty: TrustIrTy::Ptr,
                    operand: V_ADDRINT,
                },
                V_ADDR,
            ),
            // loaded = *addr : i64
            node(
                Inst::Load {
                    ty: TrustIrTy::I64,
                    ptr: V_ADDR,
                    volatile: false,
                    align: None,
                },
                V_LOADED,
            ),
        ]
    }

    /// Build the (spec, bridge) sequences a drain would discharge: the layout
    /// SPEC designates `slot + spec_offset` (width 8); the bridge side is the
    /// FOLDED emitted load (at `emit_offset`) with the SHARED harness prepended.
    fn obligation(spec_offset: u64, emit_offset: i128) -> (Vec<MirMemOp>, Vec<MirMemOp>) {
        let (harness, spec_ops) = field_load_obligation(mem_base_name(SLOT), spec_offset, 8);
        let folded = fold_emitted_mem_ops(&emitted_field_load(emit_offset)).expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        (spec_ops, bridge)
    }

    #[test]
    fn fold_reconstructs_base_plus_offset() {
        let ops = fold_emitted_mem_ops(&emitted_field_load(16)).expect("in slice");
        assert_eq!(ops.len(), 1, "exactly one load reconstructed, got {ops:?}");
        match &ops[0] {
            MirMemOp::Load { addr, width, .. } => {
                assert_eq!(addr.base, mem_base_name(SLOT), "base reconstructed as the slot");
                assert_eq!(addr.offset, 16, "offset folded from Const*1 + base");
                assert_eq!(*width, 8, "width from the emitted I64 Load");
            }
            other => panic!("expected a Load, got {other:?}"),
        }
    }

    /// POSITIVE control: the CORRECT emitted load (offset 16) folds to a bridge
    /// sequence that the layout SPEC (offset 16) does NOT refute. With a solver
    /// it Refines; with none it is Inconclusive (a 64-bit base is not
    /// exhaustively decidable) — either way, NOT Refuted.
    #[test]
    fn correct_field_load_is_not_refuted() {
        let (spec, bridge) = obligation(16, 16);
        let outcome = check_memory_sequence(
            "p1_field_load_correct",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "correct field load must not be refuted, got {outcome:?}"
        );
        // When a solver is present the obligation discharges genuinely.
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct field load must Refine, got {outcome:?}"
            );
        }
    }

    /// ANTI-TAUTOLOGY (the critical check): the bridge EMITS the load at the
    /// WRONG byte offset (8 instead of the layout-designated 16). The fold
    /// reconstructs offset 8 from the emitted Const, so the bridge sequence
    /// reads a DIFFERENT cell than the spec -> REFUTED. (No solver needed: a
    /// distinct fixed offset is decided by the array VC / sampler.)
    #[test]
    fn wrong_offset_field_load_is_refuted() {
        // Layout designates offset 16; the bridge EMITS offset 8 (a distinct
        // 8-byte cell). The fold reconstructs offset 8 from the emitted Const.
        let (spec, bridge) = obligation(16, 8);
        let outcome = check_memory_sequence(
            "p1_field_load_wrong_offset",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong EMITTED offset must be REFUTED (else the proof is a tautology), got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bridge loads through a SWAPPED base (a different
    /// `ValueId` than the slot). The fold names it as a distinct symbolic base,
    /// so the bridge load reads an unconstrained different memory than the spec
    /// -> REFUTED.
    #[test]
    fn swapped_base_field_load_is_refuted() {
        // Layout designates `mem_base_v7 + 16`; the bridge loads through a
        // DIFFERENT base (`mem_base_v999`). The harness conditions only the slot
        // cell, so the swapped-base load reads an unconstrained different memory.
        let (harness, spec) = field_load_obligation(mem_base_name(SLOT), 16, 8);
        let mut bridge = harness;
        bridge.push(MirMemOp::Load {
            addr: MemAddr {
                base: mem_base_name(ValueId::new(999)),
                offset: 16,
            },
            width: 8,
            dst: "impl_load0".into(),
        });
        let outcome = check_memory_sequence(
            "p1_field_load_swapped_base",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped base must be REFUTED, got {outcome:?}"
        );
    }

    /// A runtime-index `Mul` (stride times a NON-constant value) is out of the
    /// fixed-offset slice: the fold bails to `None` (skip), never guesses.
    #[test]
    fn runtime_index_is_out_of_slice() {
        let mut nodes = emitted_field_load(16);
        // Replace the stride const with a load result (a non-constant operand),
        // so `idx64 * stride` has a base-typed (non-Int) operand -> bail.
        nodes[4] = node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: SLOT,
                volatile: false,
                align: None,
            },
            V_STRIDE,
        );
        assert!(
            fold_emitted_mem_ops(&nodes).is_none(),
            "a non-constant stride must take the fold out of slice"
        );
    }

    // =======================================================================
    // FIELD STORE (`o.b.x = v`): the EMITTED store must write `v` to exactly the
    // layout-designated byte range and leave the sibling cells unchanged. The
    // IMPL fold reconstructs the store's offset/width/value from the real emitted
    // ops; the SPEC pins old sibling values + stores `v` at the target. A wrong
    // offset / width / value, or a sibling CLOBBER, must REFUTE.
    // =======================================================================

    /// The lowered SSA value the emitted store writes (an external value).
    const V_STOREVAL: ValueId = ValueId::new(40);

    /// The EXACT instruction sequence the bridge emits for a fixed-offset scalar
    /// field STORE `*(T*)(slot + offset) = v` (mirrors `memory_place_address` ->
    /// `emit_i64_const` + `emit_element_addr` + `emit_typed_store`): the SAME
    /// address arithmetic as the load path, terminated by a typed `Store`.
    fn emitted_field_store(offset: i128, store_ty: TrustIrTy) -> Vec<InstrNode> {
        let mut nodes = emitted_field_load(offset);
        // Swap the trailing typed Load for the typed Store of `V_STOREVAL`.
        nodes.pop();
        nodes.push(InstrNode::new(Inst::Store {
            ty: store_ty,
            ptr: V_ADDR,
            value: V_STOREVAL,
            volatile: false,
            align: None,
        }));
        nodes
    }

    /// Build the (spec, bridge) sequences a drain would discharge for a field
    /// STORE: the layout SPEC stores `v` at `slot + spec_offset` (leaving the
    /// `siblings` pinned old); the bridge side is the FOLDED emitted store (at
    /// `emit_offset`, width from `store_ty`) with the shared sibling harness
    /// prepended.
    fn store_obligation(
        spec_offset: u64,
        spec_width: u32,
        emit_offset: i128,
        store_ty: TrustIrTy,
        siblings: &[(u64, u32)],
    ) -> (Vec<MirMemOp>, Vec<MirMemOp>) {
        let (harness, spec_ops) =
            field_store_obligation(mem_base_name(SLOT), spec_offset, spec_width, V_STOREVAL, siblings);
        let folded = fold_emitted_mem_ops(&emitted_field_store(emit_offset, store_ty)).expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        (spec_ops, bridge)
    }

    #[test]
    fn fold_reconstructs_field_store() {
        let ops = fold_emitted_mem_ops(&emitted_field_store(16, TrustIrTy::I64)).expect("in slice");
        assert_eq!(ops.len(), 1, "exactly one store reconstructed, got {ops:?}");
        match &ops[0] {
            MirMemOp::Store { addr, width, value } => {
                assert_eq!(addr.base, mem_base_name(SLOT), "base reconstructed as the slot");
                assert_eq!(addr.offset, 16, "offset folded from Const*1 + base");
                assert_eq!(*width, 8, "width from the emitted I64 Store");
                assert_eq!(
                    value,
                    &SmtExpr::var(mem_store_value_name(V_STOREVAL, 8), 64),
                    "stored value named (with width) so the spec drives the same var"
                );
            }
            other => panic!("expected a Store, got {other:?}"),
        }
    }

    /// POSITIVE control: the CORRECT emitted store (offset 16, width 8) writes the
    /// value the layout SPEC designates and leaves the pinned sibling (offset 24)
    /// unchanged -> NOT refuted (Refines with a solver).
    #[test]
    fn correct_field_store_is_not_refuted() {
        let (spec, bridge) = store_obligation(16, 8, 16, TrustIrTy::I64, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_field_store_correct",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "correct field store must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct field store must Refine, got {outcome:?}"
            );
        }
    }

    /// ANTI-TAUTOLOGY: the bridge EMITS the store at the WRONG byte offset (8
    /// instead of the layout-designated 16). The folded store writes a DIFFERENT
    /// cell, so the spec's `v` at the target meets the bridge's untouched default
    /// (and the bridge writes a cell the spec leaves alone) -> REFUTED.
    #[test]
    fn wrong_offset_field_store_is_refuted() {
        let (spec, bridge) = store_obligation(16, 8, 8, TrustIrTy::I64, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_field_store_wrong_offset",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong EMITTED store offset must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bridge stores at the WRONG width (I32 = 4 bytes where
    /// the layout leaf is 8). The folded store spans a different byte range with a
    /// distinct value var, so the spec's 8-byte `v` is not reproduced -> REFUTED.
    #[test]
    fn wrong_width_field_store_is_refuted() {
        let (spec, bridge) = store_obligation(16, 8, 16, TrustIrTy::I32, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_field_store_wrong_width",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong EMITTED store width must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bridge stores the WRONG value (a different SSA value
    /// than the one the MIR designates). The folded store names a different value
    /// var than the spec's `v` -> REFUTED.
    #[test]
    fn swapped_value_field_store_is_refuted() {
        let (harness, spec) =
            field_store_obligation(mem_base_name(SLOT), 16, 8, V_STOREVAL, &[(24, 8)]);
        let mut bridge = harness;
        // The bridge writes the RIGHT cell/width but a DIFFERENT value (v999).
        bridge.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(SLOT),
                offset: 16,
            },
            value: SmtExpr::var(mem_store_value_name(ValueId::new(999), 8), 64),
            width: 8,
        });
        let outcome = check_memory_sequence(
            "p1_field_store_swapped_value",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped stored value must be REFUTED, got {outcome:?}"
        );
    }

    /// DISJOINTNESS / SIBLING-UNCHANGED (the critical safety check): the bridge
    /// writes the target field CORRECTLY but ALSO clobbers the sibling cell
    /// (`o.b.y` at offset 24). The spec preserves the pinned old sibling value, so
    /// the extra bridge write is observable -> REFUTED.
    #[test]
    fn sibling_clobber_field_store_is_refuted() {
        let (harness, spec) =
            field_store_obligation(mem_base_name(SLOT), 16, 8, V_STOREVAL, &[(24, 8)]);
        let mut bridge = harness;
        // Correct target write ...
        bridge.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(SLOT),
                offset: 16,
            },
            value: SmtExpr::var(mem_store_value_name(V_STOREVAL, 8), 64),
            width: 8,
        });
        // ... but ALSO clobbers the sibling at offset 24.
        bridge.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(SLOT),
                offset: 24,
            },
            value: SmtExpr::var(mem_store_value_name(ValueId::new(777), 8), 64),
            width: 8,
        });
        let outcome = check_memory_sequence(
            "p1_field_store_sibling_clobber",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "clobbering a sibling field must be REFUTED (disjointness), got {outcome:?}"
        );
    }

    // =======================================================================
    // MULTI-LANE AGGREGATE COPY (`dst = src`): the SEQUENCE of emitted
    // `load src+off; store dst+off` lane pairs must copy every leaf to the right
    // offset/width. The IMPL fold captures the load->store dataflow by NAMING
    // (a dst cell gets the named contents of its source cell). A DROPPED lane, a
    // WRONG lane offset, or a SWAPPED src/dst must REFUTE.
    // =======================================================================

    const SLOT_SRC: ValueId = ValueId::new(50);
    const SLOT_DST: ValueId = ValueId::new(51);

    fn store_ty_of(width: u32) -> TrustIrTy {
        match width {
            1 => TrustIrTy::I8,
            2 => TrustIrTy::I16,
            4 => TrustIrTy::I32,
            8 => TrustIrTy::I64,
            other => panic!("unsupported lane width {other}"),
        }
    }

    /// Mint the `emit_i64_const` + `emit_element_addr` address-arithmetic nodes
    /// for `base + offset` with FRESH result ids from `next`, returning the
    /// computed address value and the nodes. Mirrors the real lane address emit.
    fn emit_addr_nodes(next: &mut u32, base: ValueId, offset: i128) -> (ValueId, Vec<InstrNode>) {
        let idx = ValueId::new(*next);
        let bp = ValueId::new(*next + 1);
        let bi = ValueId::new(*next + 2);
        let idx64 = ValueId::new(*next + 3);
        let stride = ValueId::new(*next + 4);
        let offv = ValueId::new(*next + 5);
        let ai = ValueId::new(*next + 6);
        let addr = ValueId::new(*next + 7);
        *next += 8;
        let nodes = vec![
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(offset),
                },
                idx,
            ),
            node(Inst::Copy { ty: TrustIrTy::Ptr, operand: base }, bp),
            node(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: TrustIrTy::Ptr,
                    dst_ty: TrustIrTy::I64,
                    operand: bp,
                },
                bi,
            ),
            node(Inst::Copy { ty: TrustIrTy::I64, operand: idx }, idx64),
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(1),
                },
                stride,
            ),
            node(
                Inst::BinOp {
                    op: TrustIrBinOp::Mul,
                    ty: TrustIrTy::I64,
                    lhs: idx64,
                    rhs: stride,
                },
                offv,
            ),
            node(
                Inst::BinOp {
                    op: TrustIrBinOp::Add,
                    ty: TrustIrTy::I64,
                    lhs: bi,
                    rhs: offv,
                },
                ai,
            ),
            node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: TrustIrTy::I64,
                    dst_ty: TrustIrTy::Ptr,
                    operand: ai,
                },
                addr,
            ),
        ];
        (addr, nodes)
    }

    /// Emit a multi-lane copy. `lane_src(lane)` gives the (base, byte offset) the
    /// lane LOADS from, or `None` to DROP the lane entirely; `lane_dst(lane)` the
    /// (base, byte offset) it STORES to. The correct copy uses `(SRC, lane*w)` and
    /// `(DST, lane*w)`; perturbations vary these.
    fn emitted_copy<F, G>(width: u32, lanes: u64, mut lane_src: F, mut lane_dst: G) -> Vec<InstrNode>
    where
        F: FnMut(u64) -> Option<(ValueId, i128)>,
        G: FnMut(u64) -> (ValueId, i128),
    {
        let store_ty = store_ty_of(width);
        let mut next = 100u32;
        let mut nodes = Vec::new();
        for lane in 0..lanes {
            let Some((src_base, src_off)) = lane_src(lane) else {
                continue;
            };
            let (dst_base, dst_off) = lane_dst(lane);
            let (src_addr, src_nodes) = emit_addr_nodes(&mut next, src_base, src_off);
            nodes.extend(src_nodes);
            let (dst_addr, dst_nodes) = emit_addr_nodes(&mut next, dst_base, dst_off);
            nodes.extend(dst_nodes);
            let loaded = ValueId::new(next);
            next += 1;
            nodes.push(node(
                Inst::Load {
                    ty: store_ty.clone(),
                    ptr: src_addr,
                    volatile: false,
                    align: None,
                },
                loaded,
            ));
            nodes.push(InstrNode::new(Inst::Store {
                ty: store_ty.clone(),
                ptr: dst_addr,
                value: loaded,
                volatile: false,
                align: None,
            }));
        }
        nodes
    }

    fn copy_discharge(name: &str, bridge_emitted: &[InstrNode], width: u32, lanes: u64) -> RefinementOutcome {
        let spec = aggregate_copy_spec(SLOT_SRC, SLOT_DST, width, lanes);
        let folded = fold_emitted_copy_ops(bridge_emitted).expect("copy in slice");
        check_memory_sequence(name, &spec, &folded, &MemCheckConfig::default(), &AYConfig::default())
            .expect("no structural error")
    }

    #[test]
    fn fold_reconstructs_copy_lanes() {
        let emitted = emitted_copy(
            8,
            3,
            |l| Some((SLOT_SRC, (l * 8) as i128)),
            |l| (SLOT_DST, (l * 8) as i128),
        );
        let ops = fold_emitted_copy_ops(&emitted).expect("copy in slice");
        assert_eq!(ops.len(), 3, "one dst store per lane (loads dropped), got {ops:?}");
        for (lane, op) in ops.iter().enumerate() {
            let off = (lane * 8) as u64;
            match op {
                MirMemOp::Store { addr, width, value } => {
                    assert_eq!(addr.base, mem_base_name(SLOT_DST));
                    assert_eq!(addr.offset, off);
                    assert_eq!(*width, 8);
                    assert_eq!(
                        value,
                        &SmtExpr::var(mem_lane_name(SLOT_SRC, off), 64),
                        "dst lane named by its source cell"
                    );
                }
                other => panic!("expected a Store, got {other:?}"),
            }
        }
    }

    /// POSITIVE control: a correct 3-lane copy is NOT refuted (Refines w/ solver).
    #[test]
    fn correct_copy_is_not_refuted() {
        let emitted = emitted_copy(
            8,
            3,
            |l| Some((SLOT_SRC, (l * 8) as i128)),
            |l| (SLOT_DST, (l * 8) as i128),
        );
        let outcome = copy_discharge("p1_copy_correct", &emitted, 8, 3);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct copy must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct copy must Refine, got {outcome:?}"
            );
        }
    }

    /// ANTI-TAUTOLOGY: lane 1 is DROPPED (no load+store). The spec keeps a dst+8
    /// store the bridge omits, so dst+8 reads the spec's value vs the bridge's
    /// untouched default -> REFUTED (a dropped lane refutes, it is not a
    /// load-count structural skip — the stores-only model has no loads).
    #[test]
    fn dropped_lane_copy_is_refuted() {
        let emitted = emitted_copy(
            8,
            3,
            |l| if l == 1 { None } else { Some((SLOT_SRC, (l * 8) as i128)) },
            |l| (SLOT_DST, (l * 8) as i128),
        );
        let outcome = copy_discharge("p1_copy_dropped_lane", &emitted, 8, 3);
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a dropped lane must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: lane 1 STORES at the wrong dst offset (16 instead of 8).
    /// dst+8 is left untouched while dst+16 is corrupted -> REFUTED.
    #[test]
    fn wrong_lane_offset_copy_is_refuted() {
        let emitted = emitted_copy(
            8,
            3,
            |l| Some((SLOT_SRC, (l * 8) as i128)),
            |l| (SLOT_DST, if l == 1 { 16 } else { (l * 8) as i128 }),
        );
        let outcome = copy_discharge("p1_copy_wrong_offset", &emitted, 8, 3);
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong lane offset must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: lane 1 reads the WRONG source cell (src+16 instead of
    /// src+8), so dst+8 is named by the wrong source -> a different value var than
    /// the spec -> REFUTED.
    #[test]
    fn wrong_source_lane_copy_is_refuted() {
        let emitted = emitted_copy(
            8,
            3,
            |l| Some((SLOT_SRC, if l == 1 { 16 } else { (l * 8) as i128 })),
            |l| (SLOT_DST, (l * 8) as i128),
        );
        let outcome = copy_discharge("p1_copy_wrong_source", &emitted, 8, 3);
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong source lane must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: src and dst are SWAPPED (load from dst, store to src). The
    /// stores hit the source slot and carry dst-sourced values -> REFUTED.
    #[test]
    fn swapped_src_dst_copy_is_refuted() {
        let emitted = emitted_copy(
            8,
            3,
            |l| Some((SLOT_DST, (l * 8) as i128)),
            |l| (SLOT_SRC, (l * 8) as i128),
        );
        let outcome = copy_discharge("p1_copy_swapped", &emitted, 8, 3);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped src/dst copy must be REFUTED, got {outcome:?}"
        );
    }

    /// A store of a value NOT loaded earlier in the slice is NOT the copy shape:
    /// the fold bails to `None` (skip, sound) rather than mismodelling it.
    #[test]
    fn copy_fold_bails_on_non_copied_store() {
        // A lone store of an external (never-loaded) value.
        let mut next = 100u32;
        let (addr, mut nodes) = emit_addr_nodes(&mut next, SLOT_DST, 0);
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::I64,
            ptr: addr,
            value: ValueId::new(900),
            volatile: false,
            align: None,
        }));
        assert!(
            fold_emitted_copy_ops(&nodes).is_none(),
            "a store of a non-loaded value is out of the copy slice"
        );
    }

    // =======================================================================
    // DEREF STORE (`(*r).field = v` / `*r = v`): the SAME single-access fold
    // (`fold_emitted_mem_ops`) + `field_store_obligation`, but the base is `r`'s
    // RUNTIME pointer VALUE, not a stack-slot pointer. The keystone NEW check is
    // BASE IDENTITY: a store whose emitted base is NOT `r`'s pointer (a different
    // arg) must REFUTE. Plus wrong offset / width / value REFUTE, and a sibling
    // clobber through the ref REFUTES (disjointness off the SAME `r_ptr`). The
    // degenerate `*r = v` (off=0) proves too.
    //
    // `R_PTR` models `r`'s runtime pointer value: an external value the emitted
    // slice never defines, so `fold_emitted_mem_ops` names its base `mem_base_v9`
    // exactly as it would for an entry-arg reference (the "faithful naming of
    // undefined values" the module doc describes). `D_PTR` is a DIFFERENT pointer
    // (a swapped base).
    // =======================================================================

    const R_PTR: ValueId = ValueId::new(9);
    const D_PTR: ValueId = ValueId::new(999);

    /// The EMITTED address arithmetic for `base + offset` (`emit_addr_nodes`
    /// mirrors `emit_element_addr`) terminated by a typed `Store` of `store_val` —
    /// exactly the shape `memory_aggregate_ref_address` + `emit_typed_store`
    /// produce for `(*r).field = v` (base = `r`'s runtime pointer value).
    fn emitted_deref_store(
        base: ValueId,
        offset: i128,
        store_ty: TrustIrTy,
        store_val: ValueId,
    ) -> Vec<InstrNode> {
        let mut next = 200u32;
        let (addr, mut nodes) = emit_addr_nodes(&mut next, base, offset);
        nodes.push(InstrNode::new(Inst::Store {
            ty: store_ty,
            ptr: addr,
            value: store_val,
            volatile: false,
            align: None,
        }));
        nodes
    }

    /// Build the (spec, bridge) sequences a drain would discharge for a `(*r).field
    /// = v` store: the SPEC stores `V_STOREVAL` at `mem_base_v{spec_base} +
    /// spec_offset` (leaving `siblings` pinned old); the bridge side is the FOLDED
    /// emitted store through `emit_base` at `emit_offset` (width from `store_ty`,
    /// value = `emit_val`).
    #[allow(clippy::too_many_arguments)]
    fn deref_store_obligation(
        spec_base: ValueId,
        spec_offset: u64,
        spec_width: u32,
        emit_base: ValueId,
        emit_offset: i128,
        store_ty: TrustIrTy,
        emit_val: ValueId,
        siblings: &[(u64, u32)],
    ) -> (Vec<MirMemOp>, Vec<MirMemOp>) {
        let (harness, spec_ops) =
            field_store_obligation(mem_base_name(spec_base), spec_offset, spec_width, V_STOREVAL, siblings);
        let folded = fold_emitted_mem_ops(&emitted_deref_store(emit_base, emit_offset, store_ty, emit_val))
            .expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        (spec_ops, bridge)
    }

    /// The fold reconstructs the deref store's base as `r`'s RUNTIME pointer value
    /// (not a slot) + the emitted byte offset + the emitted width.
    #[test]
    fn fold_reconstructs_deref_store_base_is_the_runtime_pointer() {
        let ops = fold_emitted_mem_ops(&emitted_deref_store(R_PTR, 16, TrustIrTy::I64, V_STOREVAL))
            .expect("in slice");
        assert_eq!(ops.len(), 1, "exactly one store reconstructed, got {ops:?}");
        match &ops[0] {
            MirMemOp::Store { addr, width, value } => {
                assert_eq!(
                    addr.base,
                    mem_base_name(R_PTR),
                    "base reconstructed as r's runtime pointer value, NOT a slot"
                );
                assert_eq!(addr.offset, 16, "offset folded from Const*1 + r_ptr");
                assert_eq!(*width, 8, "width from the emitted I64 Store");
                assert_eq!(value, &SmtExpr::var(mem_store_value_name(V_STOREVAL, 8), 64));
            }
            other => panic!("expected a Store, got {other:?}"),
        }
    }

    /// POSITIVE control: the CORRECT `(*r).field = v` (base = r's pointer, offset
    /// 16, width 8) writes the layout-designated value and leaves the pinned
    /// sibling (offset 24) unchanged -> NOT refuted (Refines with a solver).
    #[test]
    fn correct_deref_field_store_is_not_refuted() {
        let (spec, bridge) =
            deref_store_obligation(R_PTR, 16, 8, R_PTR, 16, TrustIrTy::I64, V_STOREVAL, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_deref_store_correct",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "correct deref field store must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct deref field store must Refine, got {outcome:?}"
            );
        }
    }

    /// ANTI-TAUTOLOGY: the bridge EMITS the deref store at the WRONG byte offset (8
    /// instead of the layout-designated 16) -> the target cell is left default and
    /// a non-target cell is corrupted -> REFUTED.
    #[test]
    fn wrong_offset_deref_store_is_refuted() {
        let (spec, bridge) =
            deref_store_obligation(R_PTR, 16, 8, R_PTR, 8, TrustIrTy::I64, V_STOREVAL, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_deref_store_wrong_offset",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong EMITTED deref-store offset must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bridge stores at the WRONG width (I32 = 4 bytes where the
    /// layout leaf is 8) -> a different byte range / value var -> REFUTED.
    #[test]
    fn wrong_width_deref_store_is_refuted() {
        let (spec, bridge) =
            deref_store_obligation(R_PTR, 16, 8, R_PTR, 16, TrustIrTy::I32, V_STOREVAL, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_deref_store_wrong_width",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong EMITTED deref-store width must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bridge stores the WRONG value (a different SSA value than
    /// the MIR designates). The folded store names a different value var than the
    /// spec's `v` -> REFUTED.
    #[test]
    fn swapped_value_deref_store_is_refuted() {
        // Right base/offset/width, but the emitted store carries v888, not V_STOREVAL.
        let (spec, bridge) = deref_store_obligation(
            R_PTR,
            16,
            8,
            R_PTR,
            16,
            TrustIrTy::I64,
            ValueId::new(888),
            &[(24, 8)],
        );
        let outcome = check_memory_sequence(
            "p1_deref_store_swapped_value",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        if alethe_crosscheck_gap(&outcome) {
            eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped deref-store value must be REFUTED, got {outcome:?}"
        );
    }

    /// BASE IDENTITY (the keystone NEW check): the bridge emits the store through a
    /// DIFFERENT base pointer (`D_PTR`) than `r`'s pointer (`R_PTR`) the SPEC
    /// designates. The fold names `mem_base_v999`; the spec anchors `mem_base_v9`.
    /// There is a model (the two runtime pointers distinct) where `r`'s target cell
    /// is left default while the spec wrote `v` -> REFUTED. A deref store MUST land
    /// in `r`'s pointee, not some other pointer's.
    #[test]
    fn swapped_base_deref_store_is_refuted() {
        let (spec, bridge) =
            deref_store_obligation(R_PTR, 16, 8, D_PTR, 16, TrustIrTy::I64, V_STOREVAL, &[(24, 8)]);
        let outcome = check_memory_sequence(
            "p1_deref_store_swapped_base",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a deref store through the WRONG base must be REFUTED (base identity), got {outcome:?}"
        );
    }

    /// DISJOINTNESS / SIBLING-UNCHANGED THROUGH THE REF: the bridge writes the
    /// target field CORRECTLY but ALSO clobbers the sibling `(*r).other` (offset 24,
    /// the SAME `r_ptr` base). The spec preserves the pinned old sibling, so the
    /// extra write is observable -> REFUTED. This proves the disjointness is
    /// modelable through a reference (all cells share the one `r_ptr` base at
    /// distinct constant offsets), not merely fail-closed.
    #[test]
    fn sibling_clobber_deref_store_is_refuted() {
        let (harness, spec) =
            field_store_obligation(mem_base_name(R_PTR), 16, 8, V_STOREVAL, &[(24, 8)]);
        let mut bridge = harness;
        // Correct target write through r's pointer ...
        bridge.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(R_PTR),
                offset: 16,
            },
            value: SmtExpr::var(mem_store_value_name(V_STOREVAL, 8), 64),
            width: 8,
        });
        // ... but ALSO clobbers the sibling at r_ptr + 24.
        bridge.push(MirMemOp::Store {
            addr: MemAddr {
                base: mem_base_name(R_PTR),
                offset: 24,
            },
            value: SmtExpr::var(mem_store_value_name(ValueId::new(777), 8), 64),
            width: 8,
        });
        let outcome = check_memory_sequence(
            "p1_deref_store_sibling_clobber",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "clobbering a sibling through the ref must be REFUTED (disjointness), got {outcome:?}"
        );
    }

    /// The DEGENERATE `*r = v` (off=0 scalar store through a reference): the emitted
    /// store addresses `r`'s pointer directly (no address arithmetic), so the fold
    /// reconstructs base = `R_PTR` + offset 0 + width from the store type.
    fn emitted_scalar_deref_store(base: ValueId, store_ty: TrustIrTy, store_val: ValueId) -> Vec<InstrNode> {
        vec![InstrNode::new(Inst::Store {
            ty: store_ty,
            ptr: base,
            value: store_val,
            volatile: false,
            align: None,
        })]
    }

    /// POSITIVE control: the CORRECT `*r = v` (base = r's pointer, offset 0, width
    /// 8, no siblings) -> NOT refuted (Refines with a solver).
    #[test]
    fn correct_scalar_deref_store_is_not_refuted() {
        let (harness, spec) = field_store_obligation(mem_base_name(R_PTR), 0, 8, V_STOREVAL, &[]);
        let folded = fold_emitted_mem_ops(&emitted_scalar_deref_store(R_PTR, TrustIrTy::I64, V_STOREVAL))
            .expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        let outcome = check_memory_sequence(
            "p1_scalar_deref_store_correct",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "correct scalar deref store must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct scalar deref store must Refine, got {outcome:?}"
            );
        }
    }

    /// ANTI-TAUTOLOGY (scalar `*r = v`): the bridge stores at the WRONG width (I32
    /// where the leaf is 8) -> a distinct value var over a different byte range ->
    /// REFUTED.
    #[test]
    fn wrong_width_scalar_deref_store_is_refuted() {
        let (harness, spec) = field_store_obligation(mem_base_name(R_PTR), 0, 8, V_STOREVAL, &[]);
        let folded = fold_emitted_mem_ops(&emitted_scalar_deref_store(R_PTR, TrustIrTy::I32, V_STOREVAL))
            .expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        let outcome = check_memory_sequence(
            "p1_scalar_deref_store_wrong_width",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong-width scalar deref store must be REFUTED, got {outcome:?}"
        );
    }

    /// BASE IDENTITY (scalar `*r = v`): the bridge stores through a DIFFERENT base
    /// (`D_PTR`) than `r`'s pointer -> REFUTED.
    #[test]
    fn swapped_base_scalar_deref_store_is_refuted() {
        let (harness, spec) = field_store_obligation(mem_base_name(R_PTR), 0, 8, V_STOREVAL, &[]);
        let folded = fold_emitted_mem_ops(&emitted_scalar_deref_store(D_PTR, TrustIrTy::I64, V_STOREVAL))
            .expect("in slice");
        let mut bridge = harness;
        bridge.extend(folded);
        let outcome = check_memory_sequence(
            "p1_scalar_deref_store_swapped_base",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &AYConfig::default(),
        )
        .expect("no structural error");
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a scalar deref store through the WRONG base must be REFUTED, got {outcome:?}"
        );
    }

    // =======================================================================
    // `split_at` VALUE-level refinement. Each test HAND-BUILDS the exact trust-ir
    // the bridge emits for `s.split_at(mid)` (`ICmp`; `store_fat_ptr` of the two
    // halves via `InsertField`; `emit_element_addr`'s Mul/Add for the right data
    // pointer; the `Sub` for the right length), folds it, and discharges the
    // reconstructed obligations against the layout-independent `split_at_spec`.
    // A CORRECT emission must NOT refute; a swapped `mid`/`len` in the `Sub`, a
    // wrong element scale, an inverted bounds `ICmp`, or a swapped-halves store
    // MUST refute (the anti-tautology keystone).
    // =======================================================================

    use trust_ir::ICmpOp;

    const SA_PTR: ValueId = ValueId::new(60);
    const SA_LEN: ValueId = ValueId::new(61);
    const SA_MID: ValueId = ValueId::new(62);
    const SA_DEST: ValueId = ValueId::new(63);
    const SA_OFF0: u64 = 0;
    const SA_OFF1: u64 = 16;

    /// Knobs to perturb the emitted split into a specific miscompile shape.
    struct SaCfg {
        /// The bounds-check comparison (correct = `Ule`, i.e. continue iff mid<=len).
        icmp_op: ICmpOp,
        /// The element scale the bridge multiplies `mid` by for the right data
        /// pointer: `None` = the `size == 1` skip path (offset IS the index).
        emit_scale: Option<i128>,
        /// `true` (correct): right len = `Sub(len, mid)`; `false`: `Sub(mid, len)`.
        sub_len_first: bool,
        /// `true`: store the halves at SWAPPED destination offsets (fst at off1).
        swap_halves: bool,
    }

    impl SaCfg {
        /// The correct emission for an `elem_size`-byte element.
        fn correct(scale: Option<i128>) -> Self {
            SaCfg {
                icmp_op: ICmpOp::Ule,
                emit_scale: scale,
                sub_len_first: true,
                swap_halves: false,
            }
        }
    }

    fn sa_fresh(next: &mut u32) -> ValueId {
        let v = ValueId::new(*next);
        *next += 1;
        v
    }

    /// Mirror `emit_element_addr(base, index, size)`: `Copy`/`PtrToInt` the base,
    /// `Copy` the index, optional `Const`+`Mul` scale, `Add`, `IntToPtr`.
    fn sa_element_addr(
        next: &mut u32,
        nodes: &mut Vec<InstrNode>,
        base: ValueId,
        index: ValueId,
        scale: Option<i128>,
    ) -> ValueId {
        let base_ptr = sa_fresh(next);
        nodes.push(node(Inst::Copy { ty: TrustIrTy::Ptr, operand: base }, base_ptr));
        let base_int = sa_fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: base_ptr,
            },
            base_int,
        ));
        let index_i64 = sa_fresh(next);
        nodes.push(node(Inst::Copy { ty: TrustIrTy::I64, operand: index }, index_i64));
        let offset = match scale {
            None => index_i64,
            Some(k) => {
                let sc = sa_fresh(next);
                nodes.push(node(
                    Inst::Const {
                        ty: TrustIrTy::I64,
                        value: Constant::Int(k),
                    },
                    sc,
                ));
                let off = sa_fresh(next);
                nodes.push(node(
                    Inst::BinOp {
                        op: TrustIrBinOp::Mul,
                        ty: TrustIrTy::I64,
                        lhs: index_i64,
                        rhs: sc,
                    },
                    off,
                ));
                off
            }
        };
        let addr_int = sa_fresh(next);
        nodes.push(node(
            Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: base_int,
                rhs: offset,
            },
            addr_int,
        ));
        let addr = sa_fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: addr_int,
            },
            addr,
        ));
        addr
    }

    /// Mirror `iter_field_addr(base, offset)`: offset 0 IS the base (no nodes).
    fn sa_field_addr(next: &mut u32, nodes: &mut Vec<InstrNode>, base: ValueId, offset: u64) -> ValueId {
        if offset == 0 {
            return base;
        }
        let idx = sa_fresh(next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(offset as i128),
            },
            idx,
        ));
        sa_element_addr(next, nodes, base, idx, None)
    }

    /// Mirror `store_fat_ptr_slot_into(field_ptr, data, meta)`: `Copy`/`PtrToInt`
    /// the data pointer, `Copy` the meta, then `InsertField` lane 0 (data) + 1 (len).
    fn sa_store_fat_ptr(
        next: &mut u32,
        nodes: &mut Vec<InstrNode>,
        field_ptr: ValueId,
        data: ValueId,
        meta: ValueId,
    ) {
        let data_ptr = sa_fresh(next);
        nodes.push(node(Inst::Copy { ty: TrustIrTy::Ptr, operand: data }, data_ptr));
        let data_int = sa_fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: data_ptr,
            },
            data_int,
        ));
        let meta_i64 = sa_fresh(next);
        nodes.push(node(Inst::Copy { ty: TrustIrTy::I64, operand: meta }, meta_i64));
        let r0 = sa_fresh(next);
        nodes.push(node(
            Inst::InsertField {
                ty: TrustIrTy::I64,
                aggregate: field_ptr,
                field: 0,
                value: data_int,
            },
            r0,
        ));
        let r1 = sa_fresh(next);
        nodes.push(node(
            Inst::InsertField {
                ty: TrustIrTy::I64,
                aggregate: field_ptr,
                field: 1,
                value: meta_i64,
            },
            r1,
        ));
    }

    /// Build the exact emitted trust-ir slice `lower_slice_split_at_call` produces
    /// for `SA_DEST = SA_PTR/SA_LEN slice . split_at(SA_MID)`, perturbed by `cfg`.
    fn sa_emit(cfg: &SaCfg) -> Vec<InstrNode> {
        let mut next = 200u32;
        let mut nodes = Vec::new();
        // ok = ICmp op(mid, len)
        let ok = sa_fresh(&mut next);
        nodes.push(node(
            Inst::ICmp {
                op: cfg.icmp_op,
                ty: TrustIrTy::I64,
                lhs: SA_MID,
                rhs: SA_LEN,
            },
            ok,
        ));
        let (fst_off, snd_off) = if cfg.swap_halves {
            (SA_OFF1, SA_OFF0)
        } else {
            (SA_OFF0, SA_OFF1)
        };
        // left = { data = ptr, len = mid }
        let fp0 = sa_field_addr(&mut next, &mut nodes, SA_DEST, fst_off);
        sa_store_fat_ptr(&mut next, &mut nodes, fp0, SA_PTR, SA_MID);
        // right_data = ptr + mid*size ; right_len = len - mid
        let right_data = sa_element_addr(&mut next, &mut nodes, SA_PTR, SA_MID, cfg.emit_scale);
        let right_len = sa_fresh(&mut next);
        let (sub_lhs, sub_rhs) = if cfg.sub_len_first {
            (SA_LEN, SA_MID)
        } else {
            (SA_MID, SA_LEN)
        };
        nodes.push(node(
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty: TrustIrTy::I64,
                lhs: sub_lhs,
                rhs: sub_rhs,
            },
            right_len,
        ));
        let fp1 = sa_field_addr(&mut next, &mut nodes, SA_DEST, snd_off);
        sa_store_fat_ptr(&mut next, &mut nodes, fp1, right_data, right_len);
        nodes
    }

    /// Discharge every split_at obligation, prioritizing a `Refuted` over any
    /// `Inconclusive` (so a wrong half REFUTES even when the correct halves are
    /// solver-undecidable without a solver). Returns `Refuted` if ANY refutes,
    /// else `Inconclusive` if any is undecided, else `Refined`.
    fn sa_discharge(name: &str, emitted: &[InstrNode], elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let folded = fold_emitted_split_at(emitted).expect("split_at in slice");
        let obligations = split_at_obligations(
            name, &folded, SA_OFF0, SA_OFF1, SA_PTR, SA_LEN, SA_MID, elem_size,
        )
        .expect("split_at obligations built");
        let cfg = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &cfg) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    #[test]
    fn fold_reconstructs_split_at() {
        use trust_cg_verify::mir_semantics::split_at_spec;
        let folded = fold_emitted_split_at(&sa_emit(&SaCfg::correct(Some(4)))).expect("in slice");
        // The four fat-ptr lanes are reconstructed at the tuple's field offsets.
        assert!(folded.store_value(SA_OFF0, 0).is_some(), "fst.data present");
        assert!(folded.store_value(SA_OFF0, 1).is_some(), "fst.len present");
        assert!(folded.store_value(SA_OFF1, 0).is_some(), "snd.data present");
        assert!(folded.store_value(SA_OFF1, 1).is_some(), "snd.len present");
        // fst.data is the receiver pointer verbatim; fst.len is `mid` verbatim.
        assert_eq!(
            folded.store_value(SA_OFF0, 0).unwrap(),
            SmtExpr::var(sa_value_name(SA_PTR), 64),
            "fst.data reconstructed as the receiver pointer"
        );
        assert_eq!(
            folded.store_value(SA_OFF0, 1).unwrap(),
            SmtExpr::var(sa_value_name(SA_MID), 64),
            "fst.len reconstructed as mid"
        );
        // snd.data == ptr + mid*4 and snd.len == len - mid, matching the spec.
        let spec = split_at_spec(
            &sa_value_name(SA_PTR),
            &sa_value_name(SA_LEN),
            &sa_value_name(SA_MID),
            4,
        );
        assert_eq!(folded.store_value(SA_OFF1, 0).unwrap(), spec.snd_data);
        assert_eq!(folded.store_value(SA_OFF1, 1).unwrap(), spec.snd_len);
    }

    /// POSITIVE control (multi-byte element): the CORRECT emission is NOT refuted
    /// (Refines with a solver; Inconclusive without, since the halves are 64-bit).
    #[test]
    fn correct_split_at_is_not_refuted() {
        let outcome = sa_discharge("split_at_correct", &sa_emit(&SaCfg::correct(Some(4))), 4);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct split_at must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct split_at must Refine, got {outcome:?}"
            );
        }
    }

    /// POSITIVE control (`size == 1` skip path, e.g. `str`/`&[u8]`): the right data
    /// pointer is `ptr + mid` with no `Mul`; NOT refuted against `elem_size == 1`.
    #[test]
    fn correct_split_at_size1_is_not_refuted() {
        let outcome = sa_discharge("split_at_size1", &sa_emit(&SaCfg::correct(None)), 1);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 split_at must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY: the right length is `Sub(mid, len)` instead of `Sub(len,
    /// mid)`. `snd.len` folds to `mid - len` where the spec has `len - mid` -> REFUTED.
    #[test]
    fn swapped_sub_split_at_is_refuted() {
        let cfg = SaCfg {
            sub_len_first: false,
            ..SaCfg::correct(Some(4))
        };
        let outcome = sa_discharge("split_at_swapped_sub", &sa_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a `Sub(mid,len)` right length must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the right data pointer is scaled by the WRONG element size
    /// (bridge multiplies by 2, the element is 4 bytes). `snd.data` folds to
    /// `ptr + mid*2` where the spec has `ptr + mid*4` -> REFUTED.
    #[test]
    fn wrong_scale_split_at_is_refuted() {
        // Emit a *2 scale but tell the obligation the element is 4 bytes.
        let outcome = sa_discharge("split_at_wrong_scale", &sa_emit(&SaCfg::correct(Some(2))), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the bounds check is INVERTED (`Uge` instead of `Ule`), so
    /// the bridge would trap on `mid < len` and pass on `mid >= len`. The trap
    /// predicate folds to the wrong comparison -> REFUTED.
    #[test]
    fn inverted_bounds_split_at_is_refuted() {
        let cfg = SaCfg {
            icmp_op: ICmpOp::Uge,
            ..SaCfg::correct(Some(4))
        };
        let outcome = sa_discharge("split_at_inverted_bounds", &sa_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted bounds check must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the two halves are stored at SWAPPED destination offsets
    /// (fst's `{ptr, mid}` lands where snd belongs and vice versa) -> the value at
    /// `off0` is `ptr + mid*size` where the spec's fst.data is `ptr` -> REFUTED.
    #[test]
    fn swapped_halves_split_at_is_refuted() {
        let cfg = SaCfg {
            swap_halves: true,
            ..SaCfg::correct(Some(4))
        };
        let outcome = sa_discharge("split_at_swapped_halves", &sa_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped-halves stores must be REFUTED, got {outcome:?}"
        );
    }

    /// A missing bounds check (no `ICmp` emitted) takes the fold OUT OF SLICE:
    /// `None` (skip, sound) — never a false `Refined`.
    #[test]
    fn missing_bounds_split_at_is_out_of_slice() {
        let mut nodes = sa_emit(&SaCfg::correct(Some(4)));
        // Drop the leading ICmp; the fold then never sets `ok` -> None.
        nodes.remove(0);
        assert!(
            fold_emitted_split_at(&nodes).is_none(),
            "a split_at without a bounds check must be out of the fold slice"
        );
    }

    // =======================================================================
    // STRIDE-ITERATOR CONSTRUCTOR (`chunks`/`windows`/`chunks_exact`/`rchunks`/
    // `rchunks_exact`) VALUE-level refinement. Each test HAND-BUILDS the exact
    // trust-ir the bridge emits for `v.chunks(n)` (`emit_element_addr`'s Mul/Add
    // for `end`, the `ICmp Ne(n, 0)`, and the three `emit_typed_store`s of
    // `{ ptr@0, end@8, n@16 }`), folds it, and discharges the reconstructed
    // obligations against the layout-independent `stride_iter_ctor_spec`. A CORRECT
    // emission must NOT refute; a dropped `n != 0` check folds to `None` (skip); a
    // wrong element scale on `end`, an `end` off the wrong base, an inverted check,
    // or a swapped ptr/end store MUST refute (the anti-tautology keystone).
    // =======================================================================

    const ST_DATA: ValueId = ValueId::new(70);
    const ST_LEN: ValueId = ValueId::new(71);
    const ST_N: ValueId = ValueId::new(72);
    const ST_DEST: ValueId = ValueId::new(73);
    const ST_WRONGBASE: ValueId = ValueId::new(74);
    const ST_PTR_OFF: u64 = 0;
    const ST_END_OFF: u64 = 8; // SLICE_ITER_END_OFFSET
    const ST_N_OFF: u64 = 16; // WINDOWS_SIZE_OFFSET

    /// Knobs to perturb the emitted constructor into a specific miscompile shape.
    struct StCfg {
        /// The non-zero-check comparison (correct = `Ne`, i.e. continue iff n != 0).
        icmp_op: ICmpOp,
        /// Whether to emit the `n != 0` check at all (`false` DROPS it — a
        /// chunks(0)-class infinite-loop bug, which must take the fold out of slice).
        emit_check: bool,
        /// The element scale the bridge multiplies `len` by for `end`: `None` = the
        /// `size == 1` skip path (the offset IS the length).
        end_scale: Option<i128>,
        /// The base `end` is computed from (correct = `ST_DATA`).
        end_base: ValueId,
        /// `true`: store the ptr/end halves at SWAPPED cursor offsets.
        swap_ptr_end: bool,
    }

    impl StCfg {
        /// The correct emission for an `elem_size`-byte element (`scale` = the
        /// stride, or `None` for the `size == 1` skip path).
        fn correct(scale: Option<i128>) -> Self {
            StCfg {
                icmp_op: ICmpOp::Ne,
                emit_check: true,
                end_scale: scale,
                end_base: ST_DATA,
                swap_ptr_end: false,
            }
        }
    }

    /// Mirror `iter_field_addr(dest, offset)` + `emit_typed_store`: offset 0 IS the
    /// slot base (no address nodes), else `Const(offset)` + `emit_element_addr`
    /// (scale 1) then the typed `Store`.
    fn st_store(
        next: &mut u32,
        nodes: &mut Vec<InstrNode>,
        dest: ValueId,
        offset: u64,
        ty: TrustIrTy,
        value: ValueId,
    ) {
        let addr = sa_field_addr(next, nodes, dest, offset);
        nodes.push(InstrNode::new(Inst::Store {
            ty,
            ptr: addr,
            value,
            volatile: false,
            align: None,
        }));
    }

    /// Build the exact emitted trust-ir slice `lower_slice_stride_iter_ctor`
    /// produces for `ST_DEST = ST_DATA/ST_LEN slice . chunks(ST_N)`, perturbed by
    /// `cfg`: the `end` element address, the (optional) `n != 0` `ICmp`, then the
    /// three `{ ptr@0, end@8, n@16 }` cursor stores.
    fn st_emit(cfg: &StCfg) -> Vec<InstrNode> {
        let mut next = 300u32;
        let mut nodes = Vec::new();
        // end = element_addr(end_base, len, scale)   (data + len*elem_size)
        let end = sa_element_addr(&mut next, &mut nodes, cfg.end_base, ST_LEN, cfg.end_scale);
        // n_zero = Const 0 ; ok = ICmp op(n, n_zero)
        if cfg.emit_check {
            let n_zero = sa_fresh(&mut next);
            nodes.push(node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(0),
                },
                n_zero,
            ));
            let ok = sa_fresh(&mut next);
            nodes.push(node(
                Inst::ICmp {
                    op: cfg.icmp_op,
                    ty: TrustIrTy::I64,
                    lhs: ST_N,
                    rhs: n_zero,
                },
                ok,
            ));
        }
        // cursor stores: ptr@0 = data, end@8 = end, n@16 = n.
        let (ptr_val, end_val) = if cfg.swap_ptr_end {
            (end, ST_DATA)
        } else {
            (ST_DATA, end)
        };
        st_store(&mut next, &mut nodes, ST_DEST, ST_PTR_OFF, TrustIrTy::Ptr, ptr_val);
        st_store(&mut next, &mut nodes, ST_DEST, ST_END_OFF, TrustIrTy::Ptr, end_val);
        st_store(&mut next, &mut nodes, ST_DEST, ST_N_OFF, TrustIrTy::I64, ST_N);
        nodes
    }

    /// Discharge every stride-iter obligation, prioritizing a `Refuted` over any
    /// `Inconclusive` (so a wrong field REFUTES even when the correct fields are
    /// solver-undecidable without a solver). Returns `Refuted` if ANY refutes, else
    /// `Inconclusive` if any is undecided, else `Refined`.
    fn st_discharge(name: &str, emitted: &[InstrNode], elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let folded = fold_emitted_stride_iter_ctor(emitted).expect("stride ctor in slice");
        let obligations = stride_iter_ctor_obligations(
            name, &folded, ST_PTR_OFF, ST_END_OFF, ST_N_OFF, ST_DATA, ST_LEN, ST_N, elem_size,
        )
        .expect("stride ctor obligations built");
        let cfg = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &cfg) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    #[test]
    fn fold_reconstructs_stride_iter_ctor() {
        let folded = fold_emitted_stride_iter_ctor(&st_emit(&StCfg::correct(Some(4)))).expect("in slice");
        // The three cursor lanes are reconstructed at their field offsets.
        assert!(folded.store_value(ST_PTR_OFF).is_some(), "ptr present");
        assert!(folded.store_value(ST_END_OFF).is_some(), "end present");
        assert!(folded.store_value(ST_N_OFF).is_some(), "n present");
        // ptr is the receiver data pointer verbatim; n is the stride verbatim.
        assert_eq!(
            folded.store_value(ST_PTR_OFF).unwrap(),
            SmtExpr::var(sa_value_name(ST_DATA), 64),
            "cursor.ptr reconstructed as the receiver data pointer"
        );
        assert_eq!(
            folded.store_value(ST_N_OFF).unwrap(),
            SmtExpr::var(sa_value_name(ST_N), 64),
            "cursor.n reconstructed as n"
        );
        // end == data + len*4, matching the spec.
        let spec = stride_iter_ctor_spec(
            &sa_value_name(ST_DATA),
            &sa_value_name(ST_LEN),
            &sa_value_name(ST_N),
            4,
        );
        assert_eq!(folded.store_value(ST_END_OFF).unwrap(), spec.end);
    }

    /// POSITIVE control (multi-byte element): the CORRECT emission is NOT refuted
    /// (Refines with a solver; Inconclusive without, since the fields are 64-bit).
    #[test]
    fn correct_stride_iter_ctor_is_not_refuted() {
        let outcome = st_discharge("stride_correct", &st_emit(&StCfg::correct(Some(4))), 4);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct stride-iter ctor must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct stride-iter ctor must Refine, got {outcome:?}"
            );
        }
    }

    /// POSITIVE control (`size == 1` skip path, e.g. `&[u8]`): `end` is `data + len`
    /// with no `Mul`; NOT refuted against `elem_size == 1`.
    #[test]
    fn correct_stride_iter_ctor_size1_is_not_refuted() {
        let outcome = st_discharge("stride_size1", &st_emit(&StCfg::correct(None)), 1);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 stride-iter ctor must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// A DROPPED `n != 0` check (no `ICmp` emitted) takes the fold OUT OF SLICE:
    /// `None` (skip, sound) — never a false `Refined`. This is the chunks(0)
    /// infinite-loop bug class: an omitted guard must never be silently accepted.
    #[test]
    fn dropped_nonzero_check_stride_iter_ctor_is_out_of_slice() {
        let cfg = StCfg {
            emit_check: false,
            ..StCfg::correct(Some(4))
        };
        assert!(
            fold_emitted_stride_iter_ctor(&st_emit(&cfg)).is_none(),
            "a stride-iter ctor without a non-zero check must be out of the fold slice"
        );
    }

    /// ANTI-TAUTOLOGY: `end` is scaled by the WRONG element size (bridge multiplies
    /// `len` by 2, the element is 4 bytes). `cursor.end` folds to `data + len*2`
    /// where the spec has `data + len*4` -> REFUTED.
    #[test]
    fn wrong_scale_stride_iter_ctor_is_refuted() {
        // Emit a *2 scale but tell the obligation the element is 4 bytes.
        let outcome = st_discharge("stride_wrong_scale", &st_emit(&StCfg::correct(Some(2))), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale on end must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: `end` is computed off a DIFFERENT base than the slice data
    /// (`ST_WRONGBASE`). `cursor.end` folds to `wrongbase + len*4` where the spec
    /// has `data + len*4` -> REFUTED.
    #[test]
    fn wrong_base_end_stride_iter_ctor_is_refuted() {
        let cfg = StCfg {
            end_base: ST_WRONGBASE,
            ..StCfg::correct(Some(4))
        };
        let outcome = st_discharge("stride_wrong_base", &st_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an end computed off the wrong base must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the non-zero check is INVERTED (`Eq` instead of `Ne`), so the
    /// bridge would trap on `n != 0` and pass on `n == 0` (the exact chunks(0) bug).
    /// The trap predicate folds to the wrong comparison -> REFUTED.
    #[test]
    fn inverted_nonzero_check_stride_iter_ctor_is_refuted() {
        let cfg = StCfg {
            icmp_op: ICmpOp::Eq,
            ..StCfg::correct(Some(4))
        };
        let outcome = st_discharge("stride_inverted_check", &st_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted non-zero check must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the ptr and end halves are stored at SWAPPED cursor offsets
    /// (`data + len*size` lands at `ptr@0` where the spec's `cursor.ptr` is `data`)
    /// -> REFUTED.
    #[test]
    fn swapped_ptr_end_stride_iter_ctor_is_refuted() {
        let cfg = StCfg {
            swap_ptr_end: true,
            ..StCfg::correct(Some(4))
        };
        let outcome = st_discharge("stride_swapped_ptr_end", &st_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped ptr/end cursor stores must be REFUTED, got {outcome:?}"
        );
    }

    // =======================================================================
    // CHECKED INDEX (`v[i]` / `&v[i]` / `&mut v[i]` — `<Vec<T> as Index>::index`
    // / `index_mut` and `<[T]>::index`) VALUE-level refinement. Each test
    // HAND-BUILDS the exact trust-ir the bridge emits for the checked path of
    // `lower_vec_index` (the bounds `ICmp Ult(i, len)`, then
    // `emit_element_addr`'s Copy/PtrToInt/Copy/[Const,Mul]/Add/IntToPtr for
    // `data + i*elem_size`), folds it, and discharges the reconstructed
    // obligations against the layout-independent `vec_index_spec`. A CORRECT
    // emission must NOT refute; a DROPPED bounds check folds to `None` (skip); an
    // inverted bounds check, a wrong element scale, or an address off the wrong
    // base MUST refute (the anti-tautology keystone). The `unsafe` unchecked
    // (`get_unchecked*`) path is never captured (the lowering gates on `checked`),
    // so it is neither falsely refuted nor falsely refined.
    // =======================================================================

    const VI_DATA: ValueId = ValueId::new(80);
    const VI_LEN: ValueId = ValueId::new(81);
    const VI_IDX: ValueId = ValueId::new(82);
    const VI_WRONGBASE: ValueId = ValueId::new(83);

    /// Knobs to perturb the emitted checked index into a specific miscompile shape.
    struct ViCfg {
        /// The bounds-check comparison (correct = `Ult`, i.e. continue iff i<len).
        icmp_op: ICmpOp,
        /// Whether to emit the `i < len` bounds check at all (`false` DROPS it — the
        /// silent-OOB-read soundness bug class, which must take the fold out of slice).
        emit_check: bool,
        /// The element scale the bridge multiplies `i` by for the address: `None` =
        /// the `size == 1` skip path (the offset IS the index).
        addr_scale: Option<i128>,
        /// The base the element address is computed from (correct = `VI_DATA`).
        addr_base: ValueId,
    }

    impl ViCfg {
        /// The correct emission for an `elem_size`-byte element (`scale` = the
        /// stride, or `None` for the `size == 1` skip path).
        fn correct(scale: Option<i128>) -> Self {
            ViCfg {
                icmp_op: ICmpOp::Ult,
                emit_check: true,
                addr_scale: scale,
                addr_base: VI_DATA,
            }
        }
    }

    /// Build the exact emitted trust-ir slice the CHECKED path of `lower_vec_index`
    /// produces: the (optional) bounds `ICmp Ult(i, len)`, then the
    /// `emit_element_addr(data, i, scale)` computation (terminal `IntToPtr`). The
    /// `len` load and `data` load are OUTSIDE this slice (external symbolic values),
    /// exactly as the real lowering excludes the `ExtractField`s.
    fn vi_emit(cfg: &ViCfg) -> Vec<InstrNode> {
        let mut next = 400u32;
        let mut nodes = Vec::new();
        if cfg.emit_check {
            let ok = sa_fresh(&mut next);
            nodes.push(node(
                Inst::ICmp {
                    op: cfg.icmp_op,
                    ty: TrustIrTy::I64,
                    lhs: VI_IDX,
                    rhs: VI_LEN,
                },
                ok,
            ));
        }
        // elem_addr = element_addr(addr_base, i, scale)   (data + i*elem_size)
        sa_element_addr(&mut next, &mut nodes, cfg.addr_base, VI_IDX, cfg.addr_scale);
        nodes
    }

    /// Discharge every vec-index obligation, prioritizing a `Refuted` over any
    /// `Inconclusive` (so a wrong field REFUTES even when the correct fields are
    /// solver-undecidable without a solver). Returns `Refuted` if ANY refutes, else
    /// `Inconclusive` if any is undecided, else `Refined`.
    fn vi_discharge(name: &str, emitted: &[InstrNode], elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let folded = fold_emitted_vec_index(emitted).expect("vec-index in slice");
        let obligations =
            vec_index_obligations(name, &folded, VI_DATA, VI_LEN, VI_IDX, elem_size)
                .expect("vec-index obligations built");
        let cfg = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &cfg) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    #[test]
    fn fold_reconstructs_vec_index() {
        let folded = fold_emitted_vec_index(&vi_emit(&ViCfg::correct(Some(4)))).expect("in slice");
        // The bounds predicate is `i <u len`, and the address is `data + i*4`.
        let spec = vec_index_spec(
            &sa_value_name(VI_DATA),
            &sa_value_name(VI_LEN),
            &sa_value_name(VI_IDX),
            4,
        );
        assert_eq!(
            folded.ok,
            SmtExpr::var(sa_value_name(VI_IDX), 64).bvult(SmtExpr::var(sa_value_name(VI_LEN), 64)),
            "bounds predicate reconstructed as `i <u len`"
        );
        assert_eq!(
            folded.elem_addr, spec.elem_addr,
            "element address reconstructed as `data + i*elem_size`"
        );
    }

    /// POSITIVE control (multi-byte element): the CORRECT emission is NOT refuted
    /// (Refines with a solver; Inconclusive without, since the fields are 64-bit).
    #[test]
    fn correct_vec_index_is_not_refuted() {
        let outcome = vi_discharge("vec_index_correct", &vi_emit(&ViCfg::correct(Some(4))), 4);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct checked index must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct checked index must Refine, got {outcome:?}"
            );
        }
    }

    /// POSITIVE control (`size == 1` skip path, e.g. `&[u8]`): the address is
    /// `data + i` with no `Mul`; NOT refuted against `elem_size == 1`.
    #[test]
    fn correct_vec_index_size1_is_not_refuted() {
        let outcome = vi_discharge("vec_index_size1", &vi_emit(&ViCfg::correct(None)), 1);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 checked index must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// A DROPPED bounds check (no `ICmp` emitted) takes the fold OUT OF SLICE:
    /// `None` (skip, sound) — never a false `Refined`. This is the exact `v[oob]`
    /// silent-OOB-read soundness bug class: an omitted guard must never be silently
    /// accepted.
    #[test]
    fn dropped_bounds_check_vec_index_is_out_of_slice() {
        let cfg = ViCfg {
            emit_check: false,
            ..ViCfg::correct(Some(4))
        };
        assert!(
            fold_emitted_vec_index(&vi_emit(&cfg)).is_none(),
            "a checked index without a bounds check must be out of the fold slice"
        );
    }

    /// ANTI-TAUTOLOGY: the bounds check is INVERTED (`Uge` instead of `Ult`), so the
    /// bridge would trap on `i < len` and pass on `i >= len` (the wrong edge — a
    /// silent OOB read). The trap predicate folds to the wrong comparison -> REFUTED.
    #[test]
    fn inverted_bounds_vec_index_is_refuted() {
        let cfg = ViCfg {
            icmp_op: ICmpOp::Uge,
            ..ViCfg::correct(Some(4))
        };
        let outcome = vi_discharge("vec_index_inverted_bounds", &vi_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted bounds check must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the address is scaled by the WRONG element size (bridge
    /// multiplies `i` by 2, the element is 4 bytes). `elem_addr` folds to
    /// `data + i*2` where the spec has `data + i*4` -> REFUTED.
    #[test]
    fn wrong_scale_vec_index_is_refuted() {
        // Emit a *2 scale but tell the obligation the element is 4 bytes.
        let outcome = vi_discharge("vec_index_wrong_scale", &vi_emit(&ViCfg::correct(Some(2))), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the address is computed off a DIFFERENT base than the slice
    /// data (`VI_WRONGBASE`). `elem_addr` folds to `wrongbase + i*4` where the spec
    /// has `data + i*4` -> REFUTED.
    #[test]
    fn wrong_base_vec_index_is_refuted() {
        let cfg = ViCfg {
            addr_base: VI_WRONGBASE,
            ..ViCfg::correct(Some(4))
        };
        let outcome = vi_discharge("vec_index_wrong_base", &vi_emit(&cfg), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an address off the wrong base must be REFUTED, got {outcome:?}"
        );
    }

    // =======================================================================
    // CHECKED Vec RANGE SUBSLICE (`&v[a..b]` / `&v[a..]` / `&v[..b]` —
    // `<Vec<T> as Index<Range|RangeFrom|RangeTo>>::index` / `index_mut`)
    // VALUE-level refinement. Each test HAND-BUILDS the exact trust-ir the bridge
    // emits for `lower_vec_range_subslice_index_call` (`emit_element_addr`'s
    // Copy/PtrToInt/Copy/[Const,Mul]/Add/IntToPtr for `data + start*elem_size`, the
    // `Sub` for `end - start`, the two `InsertField`s of `{ data@0/0, len@0/1 }`, and
    // the COMBINED bounds check — two `ICmp Ule`s + a Bool `And`), folds it, and
    // discharges the reconstructed obligations against the layout-independent
    // `vec_range_subslice_spec`. A CORRECT emission (each of the three forms, and the
    // `size == 1` control) must NOT refute; a DROPPED bounds check folds to `None`
    // (skip); an INVERTED bound, an INCOMPLETE (single-comparison) check, a wrong
    // element scale, a wrong `Sub` direction, or a pointer off the wrong base MUST
    // refute (the anti-tautology keystone).
    // =======================================================================

    const VR_DATA: ValueId = ValueId::new(90);
    const VR_LEN: ValueId = ValueId::new(91);
    const VR_A: ValueId = ValueId::new(92);
    const VR_B: ValueId = ValueId::new(93);
    const VR_DEST: ValueId = ValueId::new(94);
    const VR_WRONGBASE: ValueId = ValueId::new(95);
    const VR_OFF: u64 = 0; // both fat-ptr lanes share the one slot base.

    /// The bounds-check emission shape to build (the anti-tautology axis).
    #[derive(Clone, Copy)]
    enum VrBounds {
        /// Correct: `ICmp Ule(start, end)` + `ICmp Ule(end, len)` + Bool `And`.
        Correct,
        /// No bounds check at all (must take the fold OUT OF SLICE — skip).
        Dropped,
        /// A single `ICmp Ule(end, len)` with NO order check and NO `And` (the
        /// incomplete-bounds miscompile — must REFUTE).
        Incomplete,
        /// The ORDER check inverted (`Uge(start, end)`) — must REFUTE.
        InvertedOrder,
    }

    /// The `(start, end, a, b)` `ValueId`s a given range form feeds the emission /
    /// obligation: `Range` = `(a, b)`; `RangeFrom` anchors `end`/`b` to `len`;
    /// `RangeTo` names `a` the `0` base and takes `end`/`b` = `b`.
    fn vr_start_end(form: RangeForm) -> (ValueId, ValueId, ValueId, ValueId) {
        match form {
            RangeForm::Range => (VR_A, VR_B, VR_A, VR_B),
            RangeForm::RangeFrom => (VR_A, VR_LEN, VR_A, VR_LEN),
            RangeForm::RangeTo => (VR_A, VR_B, VR_A, VR_B),
        }
    }

    /// Knobs to perturb the emitted range subslice into a specific miscompile shape.
    struct VrCfg {
        form: RangeForm,
        /// The element scale the bridge multiplies `start` by for the result pointer:
        /// `None` = the `size == 1` skip path (offset IS the index).
        scale: Option<i128>,
        /// The base the result pointer is computed from (correct = `VR_DATA`).
        base: ValueId,
        /// `true` (correct): result len = `Sub(end, start)`; `false`: `Sub(start, end)`.
        sub_len_first: bool,
        /// The bounds-check emission shape.
        bounds: VrBounds,
    }

    impl VrCfg {
        /// The correct emission for `form` and an `elem_size`-byte element (`scale` =
        /// the stride, or `None` for the `size == 1` skip path).
        fn correct(form: RangeForm, scale: Option<i128>) -> Self {
            VrCfg {
                form,
                scale,
                base: VR_DATA,
                sub_len_first: true,
                bounds: VrBounds::Correct,
            }
        }
    }

    /// Build the exact emitted trust-ir slice `lower_vec_range_subslice_index_call`
    /// produces for `VR_DEST = &(VR_DATA/VR_LEN)[range]`, perturbed by `cfg`: the
    /// result-pointer element address, the length `Sub`, the two `{data,len}`
    /// `InsertField` stores, then the COMBINED bounds check (EXCLUDING the `CondBr`).
    fn vr_emit(cfg: &VrCfg) -> Vec<InstrNode> {
        let mut next = 500u32;
        let mut nodes = Vec::new();
        let (start, end, _a, _b) = vr_start_end(cfg.form);
        // sub_data = element_addr(base, start, scale)   (data + start*elem_size)
        let sub_data = sa_element_addr(&mut next, &mut nodes, cfg.base, start, cfg.scale);
        // sub_len = Sub(end, start)  [correct]  or  Sub(start, end).
        let sub_len = sa_fresh(&mut next);
        let (sub_lhs, sub_rhs) = if cfg.sub_len_first {
            (end, start)
        } else {
            (start, end)
        };
        nodes.push(node(
            Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty: TrustIrTy::I64,
                lhs: sub_lhs,
                rhs: sub_rhs,
            },
            sub_len,
        ));
        // store_fat_ptr_slot_into(VR_DEST, sub_data, sub_len): InsertField 0/1.
        sa_store_fat_ptr(&mut next, &mut nodes, VR_DEST, sub_data, sub_len);
        // Combined bounds check.
        match cfg.bounds {
            VrBounds::Dropped => {}
            VrBounds::Incomplete => {
                // Single `end <= len` — no order check, no `And`.
                let end_le_len = sa_fresh(&mut next);
                nodes.push(node(
                    Inst::ICmp {
                        op: ICmpOp::Ule,
                        ty: TrustIrTy::I64,
                        lhs: end,
                        rhs: VR_LEN,
                    },
                    end_le_len,
                ));
            }
            VrBounds::Correct | VrBounds::InvertedOrder => {
                let order_op = if matches!(cfg.bounds, VrBounds::InvertedOrder) {
                    ICmpOp::Uge
                } else {
                    ICmpOp::Ule
                };
                let start_le_end = sa_fresh(&mut next);
                nodes.push(node(
                    Inst::ICmp {
                        op: order_op,
                        ty: TrustIrTy::I64,
                        lhs: start,
                        rhs: end,
                    },
                    start_le_end,
                ));
                let end_le_len = sa_fresh(&mut next);
                nodes.push(node(
                    Inst::ICmp {
                        op: ICmpOp::Ule,
                        ty: TrustIrTy::I64,
                        lhs: end,
                        rhs: VR_LEN,
                    },
                    end_le_len,
                ));
                let ok = sa_fresh(&mut next);
                nodes.push(node(
                    Inst::BinOp {
                        op: TrustIrBinOp::And,
                        ty: TrustIrTy::Bool,
                        lhs: start_le_end,
                        rhs: end_le_len,
                    },
                    ok,
                ));
            }
        }
        nodes
    }

    /// Discharge every range-subslice obligation, prioritizing a `Refuted` over any
    /// `Inconclusive` (so a wrong field REFUTES even when the correct fields are
    /// solver-undecidable without a solver). Returns `Refuted` if ANY refutes, else
    /// `Inconclusive` if any is undecided, else `Refined`.
    fn vr_discharge(name: &str, cfg: &VrCfg, elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let folded = fold_emitted_vec_range_subslice(&vr_emit(cfg)).expect("vec-subslice in slice");
        let (_start, _end, a, b) = vr_start_end(cfg.form);
        let obligations = vec_range_subslice_obligations(
            name, &folded, cfg.form, VR_OFF, VR_DATA, VR_LEN, a, b, elem_size,
        )
        .expect("vec-subslice obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    #[test]
    fn fold_reconstructs_vec_range_subslice() {
        let cfg = VrCfg::correct(RangeForm::Range, Some(4));
        let folded = fold_emitted_vec_range_subslice(&vr_emit(&cfg)).expect("in slice");
        // The two fat-ptr lanes are reconstructed at the slot base (offset 0).
        let spec = vec_range_subslice_spec(
            RangeForm::Range,
            &sa_value_name(VR_DATA),
            &sa_value_name(VR_LEN),
            &sa_value_name(VR_A),
            &sa_value_name(VR_B),
            4,
        );
        assert_eq!(
            folded.store_value(VR_OFF, 0).unwrap(),
            spec.result_ptr,
            "result ptr reconstructed as `data + start*elem_size`"
        );
        assert_eq!(
            folded.store_value(VR_OFF, 1).unwrap(),
            spec.result_len,
            "result len reconstructed as `end - start`"
        );
        // ok = (a <=u b) AND (b <=u len).
        assert_eq!(
            folded.ok,
            SmtExpr::var(sa_value_name(VR_A), 64)
                .bvule(SmtExpr::var(sa_value_name(VR_B), 64))
                .and_expr(
                    SmtExpr::var(sa_value_name(VR_B), 64)
                        .bvule(SmtExpr::var(sa_value_name(VR_LEN), 64))
                ),
            "combined bounds predicate reconstructed as `(a<=b) && (b<=len)`"
        );
    }

    /// POSITIVE control (`&v[a..b]`, multi-byte element): NOT refuted (Refines with a
    /// solver; Inconclusive without, since the fields are 64-bit).
    #[test]
    fn correct_vec_range_subslice_range_is_not_refuted() {
        let outcome = vr_discharge(
            "vr_range_correct",
            &VrCfg::correct(RangeForm::Range, Some(4)),
            4,
        );
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct `a..b` subslice must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(
                matches!(outcome, RefinementOutcome::Refined),
                "with a solver the correct `a..b` subslice must Refine, got {outcome:?}"
            );
        }
    }

    /// POSITIVE control (`&v[a..]`, open end anchored to `len`): NOT refuted.
    #[test]
    fn correct_vec_range_subslice_from_is_not_refuted() {
        let outcome = vr_discharge(
            "vr_from_correct",
            &VrCfg::correct(RangeForm::RangeFrom, Some(4)),
            4,
        );
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct `a..` subslice must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE control (`&v[..b]`, open start): NOT refuted.
    #[test]
    fn correct_vec_range_subslice_to_is_not_refuted() {
        let outcome = vr_discharge(
            "vr_to_correct",
            &VrCfg::correct(RangeForm::RangeTo, Some(4)),
            4,
        );
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct `..b` subslice must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE control (`size == 1` skip path, e.g. `&[u8]`): the pointer is
    /// `data + start` with no `Mul`; NOT refuted against `elem_size == 1`.
    #[test]
    fn correct_vec_range_subslice_size1_is_not_refuted() {
        let outcome = vr_discharge(
            "vr_range_size1",
            &VrCfg::correct(RangeForm::Range, None),
            1,
        );
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 subslice must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// A DROPPED bounds check (no `ICmp`/`And` emitted) takes the fold OUT OF SLICE:
    /// `None` (skip, sound) — never a false `Refined`.
    #[test]
    fn dropped_bounds_vec_range_subslice_is_out_of_slice() {
        let cfg = VrCfg {
            bounds: VrBounds::Dropped,
            ..VrCfg::correct(RangeForm::Range, Some(4))
        };
        assert!(
            fold_emitted_vec_range_subslice(&vr_emit(&cfg)).is_none(),
            "a subslice without a bounds check must be out of the fold slice"
        );
    }

    /// ANTI-TAUTOLOGY: the ORDER bound is INVERTED (`Uge(start,end)` instead of
    /// `Ule`), so the bridge would trap on `start < end` — the trap predicate folds to
    /// the wrong comparison -> REFUTED.
    #[test]
    fn inverted_bounds_vec_range_subslice_is_refuted() {
        let cfg = VrCfg {
            bounds: VrBounds::InvertedOrder,
            ..VrCfg::correct(RangeForm::Range, Some(4))
        };
        let outcome = vr_discharge("vr_inverted", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted bounds check must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: an INCOMPLETE check (only `end <= len`, dropping the `start <=
    /// end` order gate and the `And`) — on `&v[a..]` where the order gate is what
    /// rejects `start > end`. The reconstructed `ok` folds to a weaker predicate than
    /// the spec's combined check -> REFUTED.
    #[test]
    fn incomplete_bounds_vec_range_subslice_is_refuted() {
        let cfg = VrCfg {
            bounds: VrBounds::Incomplete,
            ..VrCfg::correct(RangeForm::RangeFrom, Some(4))
        };
        let outcome = vr_discharge("vr_incomplete", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an incomplete (single-comparison) bounds check must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the result pointer is scaled by the WRONG element size (bridge
    /// multiplies `start` by 2, the element is 4 bytes) — on `&v[..b]`. `result_ptr`
    /// folds to `data + start*2` where the spec has `data + start*4` -> REFUTED.
    #[test]
    fn wrong_scale_vec_range_subslice_is_refuted() {
        // Emit a *2 scale but tell the obligation the element is 4 bytes.
        let outcome = vr_discharge(
            "vr_wrong_scale",
            &VrCfg::correct(RangeForm::RangeTo, Some(2)),
            4,
        );
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the result length is `Sub(start, end)` instead of `Sub(end,
    /// start)`. `result_len` folds to `start - end` where the spec has `end - start`
    /// -> REFUTED.
    #[test]
    fn wrong_sub_direction_vec_range_subslice_is_refuted() {
        let cfg = VrCfg {
            sub_len_first: false,
            ..VrCfg::correct(RangeForm::Range, Some(4))
        };
        let outcome = vr_discharge("vr_wrong_sub", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a `Sub(start,end)` result length must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the result pointer is computed off a DIFFERENT base than the
    /// slice data (`VR_WRONGBASE`). `result_ptr` folds to `wrongbase + start*4` where
    /// the spec has `data + start*4` -> REFUTED.
    #[test]
    fn wrong_base_vec_range_subslice_is_refuted() {
        let cfg = VrCfg {
            base: VR_WRONGBASE,
            ..VrCfg::correct(RangeForm::Range, Some(4))
        };
        let outcome = vr_discharge("vr_wrong_base", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a result pointer off the wrong base must be REFUTED, got {outcome:?}"
        );
    }

    // =======================================================================
    // Lane 5: niche `Option<&T>` first/last (the `Select -> ITE` primitive).
    // The emitter hand-builds the EXACT shape `lower_slice_first_last_call`
    // emits (the `ICmp Ne(len,0)`, the element-address arithmetic, the null
    // `None` `IntToPtr`, the `Select`, and the niche `Store`), so the fold's
    // reconstruction is exercised against the spec end to end.
    // =======================================================================
    const FL_DATA: ValueId = ValueId::new(90);
    const FL_LEN: ValueId = ValueId::new(91);
    const FL_SLOT: ValueId = ValueId::new(94);
    const FL_WRONGBASE: ValueId = ValueId::new(95);

    #[derive(Clone)]
    struct FlCfg {
        kind: SliceEndKind,
        /// The emptiness comparison (`Ne` = correct `len != 0`).
        cond_op: ICmpOp,
        /// The `None` niche integer (`0` = correct null).
        none_val: i128,
        /// `Last` only: subtract 1 for the last index (`true` = correct).
        last_minus_one: bool,
        /// `Last` only: the element-address `Mul` constant (= `elem_size` correct).
        scale: i128,
        /// The base the element pointer is computed from (`FL_DATA` = correct).
        base: ValueId,
        /// Store the element pointer WITHOUT a `Select` (drop the `None` edge).
        unconditional: bool,
    }

    impl FlCfg {
        fn correct(kind: SliceEndKind, scale: i128) -> Self {
            Self {
                kind,
                cond_op: ICmpOp::Ne,
                none_val: 0,
                last_minus_one: true,
                scale,
                base: FL_DATA,
                unconditional: false,
            }
        }
    }

    fn fl_emit(cfg: &FlCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 100u32;
        let mut fresh = || {
            let v = ValueId::new(next);
            next += 1;
            v
        };
        // zero = const 0 ; cond = ICmp <op>(len, zero).
        let zero = fresh();
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0),
            },
            zero,
        ));
        let cond = fresh();
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: cfg.cond_op,
                ty: TrustIrTy::I64,
                lhs: FL_LEN,
                rhs: zero,
            })
            .with_result(cond),
        );
        // The yielded element pointer.
        let elem_ptr = match cfg.kind {
            SliceEndKind::First => cfg.base,
            SliceEndKind::Last => {
                let idx = if cfg.last_minus_one {
                    let one = fresh();
                    nodes.push(node(
                        Inst::Const {
                            ty: TrustIrTy::I64,
                            value: Constant::Int(1),
                        },
                        one,
                    ));
                    let li = fresh();
                    nodes.push(
                        InstrNode::new(Inst::BinOp {
                            op: TrustIrBinOp::Sub,
                            ty: TrustIrTy::I64,
                            lhs: FL_LEN,
                            rhs: one,
                        })
                        .with_result(li),
                    );
                    li
                } else {
                    FL_LEN
                };
                // emit_element_addr(base, idx, scale).
                let bp = fresh();
                nodes.push(node(
                    Inst::Copy {
                        ty: TrustIrTy::Ptr,
                        operand: cfg.base,
                    },
                    bp,
                ));
                let bi = fresh();
                nodes.push(node(
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        src_ty: TrustIrTy::Ptr,
                        dst_ty: TrustIrTy::I64,
                        operand: bp,
                    },
                    bi,
                ));
                let i64v = fresh();
                nodes.push(node(
                    Inst::Copy {
                        ty: TrustIrTy::I64,
                        operand: idx,
                    },
                    i64v,
                ));
                let stride = fresh();
                nodes.push(node(
                    Inst::Const {
                        ty: TrustIrTy::I64,
                        value: Constant::Int(cfg.scale),
                    },
                    stride,
                ));
                let offv = fresh();
                nodes.push(
                    InstrNode::new(Inst::BinOp {
                        op: TrustIrBinOp::Mul,
                        ty: TrustIrTy::I64,
                        lhs: i64v,
                        rhs: stride,
                    })
                    .with_result(offv),
                );
                let ai = fresh();
                nodes.push(
                    InstrNode::new(Inst::BinOp {
                        op: TrustIrBinOp::Add,
                        ty: TrustIrTy::I64,
                        lhs: bi,
                        rhs: offv,
                    })
                    .with_result(ai),
                );
                let p = fresh();
                nodes.push(node(
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        src_ty: TrustIrTy::I64,
                        dst_ty: TrustIrTy::Ptr,
                        operand: ai,
                    },
                    p,
                ));
                p
            }
        };
        // chosen = cond ? elem_ptr : none_ptr   (or elem_ptr unconditionally).
        let chosen = if cfg.unconditional {
            elem_ptr
        } else {
            let none_int = fresh();
            nodes.push(node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(cfg.none_val),
                },
                none_int,
            ));
            let none_ptr = fresh();
            nodes.push(node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: TrustIrTy::I64,
                    dst_ty: TrustIrTy::Ptr,
                    operand: none_int,
                },
                none_ptr,
            ));
            let ch = fresh();
            nodes.push(
                InstrNode::new(Inst::Select {
                    ty: TrustIrTy::Ptr,
                    cond,
                    then_val: elem_ptr,
                    else_val: none_ptr,
                })
                .with_result(ch),
            );
            ch
        };
        // The niche store into the Option<&T> slot.
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::Ptr,
            ptr: FL_SLOT,
            value: chosen,
            volatile: false,
            align: None,
        }));
        nodes
    }

    fn fl_discharge(name: &str, cfg: &FlCfg, elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let folded = fold_emitted_slice_first_last(&fl_emit(cfg)).expect("first/last in slice");
        let obligations =
            slice_first_last_obligations(name, &folded, cfg.kind, FL_DATA, FL_LEN, elem_size)
                .expect("first/last obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs `first` as `ITE(len != 0, data, 0)`.
    #[test]
    fn fold_reconstructs_slice_first() {
        let cfg = FlCfg::correct(SliceEndKind::First, 4);
        let folded = fold_emitted_slice_first_last(&fl_emit(&cfg)).expect("in slice");
        let spec = slice_first_last_spec(
            SliceEndKind::First,
            &sa_value_name(FL_DATA),
            &sa_value_name(FL_LEN),
            4,
        );
        assert_eq!(folded.niche, spec.niche);
    }

    /// POSITIVE: a correct `first` is NOT refuted.
    #[test]
    fn correct_slice_first_is_not_refuted() {
        let outcome = fl_discharge("fl_first", &FlCfg::correct(SliceEndKind::First, 4), 4);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct first must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct `last` (index `len-1`, scale = elem_size) is NOT refuted.
    #[test]
    fn correct_slice_last_is_not_refuted() {
        let outcome = fl_discharge("fl_last", &FlCfg::correct(SliceEndKind::Last, 4), 4);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct last must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE control (`size == 1`, e.g. `&[u8]`): `last` is `data + (len-1)*1`.
    #[test]
    fn correct_slice_last_size1_is_not_refuted() {
        let outcome = fl_discharge("fl_last_s1", &FlCfg::correct(SliceEndKind::Last, 1), 1);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 last must not be refuted, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the emptiness test is INVERTED (`Eq(len,0)` instead of `Ne`),
    /// so the bridge would yield `Some` on an EMPTY slice. The folded `ITE` condition
    /// is `len == 0` where the spec has `len != 0` -> REFUTED.
    #[test]
    fn inverted_cond_slice_first_is_refuted() {
        let cfg = FlCfg {
            cond_op: ICmpOp::Eq,
            ..FlCfg::correct(SliceEndKind::First, 4)
        };
        let outcome = fl_discharge("fl_inverted", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted emptiness test must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the `None` niche is NON-NULL (`0xff` instead of `0`), so an
    /// empty slice would decode to `Some(0xff)`. The folded `else` branch is `0xff`
    /// where the spec has `0` -> REFUTED.
    #[test]
    fn nonnull_none_slice_first_is_refuted() {
        let cfg = FlCfg {
            none_val: 0xff,
            ..FlCfg::correct(SliceEndKind::First, 4)
        };
        let outcome = fl_discharge("fl_nonnull_none", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a non-null None niche must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: `last` forgets the `-1` (indexes `data + len*size` instead of
    /// `data + (len-1)*size`) — a one-past-the-end read. The folded pointer differs
    /// from the spec's `data + (len-1)*size` -> REFUTED.
    #[test]
    fn wrong_last_index_is_refuted() {
        let cfg = FlCfg {
            last_minus_one: false,
            ..FlCfg::correct(SliceEndKind::Last, 4)
        };
        let outcome = fl_discharge("fl_wrong_idx", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a last index off by one (no -1) must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: `last` scales the index by the WRONG element size (bridge
    /// multiplies by 2, the element is 4 bytes) -> REFUTED.
    #[test]
    fn wrong_scale_slice_last_is_refuted() {
        let outcome = fl_discharge("fl_wrong_scale", &FlCfg::correct(SliceEndKind::Last, 2), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the element pointer is off a DIFFERENT base than the slice
    /// data (`last` off `FL_WRONGBASE`) -> REFUTED.
    #[test]
    fn wrong_base_slice_last_is_refuted() {
        let cfg = FlCfg {
            base: FL_WRONGBASE,
            ..FlCfg::correct(SliceEndKind::Last, 4)
        };
        let outcome = fl_discharge("fl_wrong_base", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an element pointer off the wrong base must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the element pointer is stored UNCONDITIONALLY (the `None` edge
    /// dropped, so an empty slice decodes to `Some(data)`). The folded niche is `data`
    /// where the spec has `ITE(len!=0, data, 0)` (they differ on `len==0`) -> REFUTED.
    #[test]
    fn unconditional_some_slice_first_is_refuted() {
        let cfg = FlCfg {
            unconditional: true,
            ..FlCfg::correct(SliceEndKind::First, 4)
        };
        let outcome = fl_discharge("fl_unconditional", &cfg, 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an unconditional (no-None) store must be REFUTED, got {outcome:?}"
        );
    }

    /// A missing niche store takes the fold OUT OF SLICE: `None` (skip, sound).
    #[test]
    fn no_store_slice_first_is_out_of_slice() {
        // Emit only the cond + a dangling select, no Store.
        let cfg = FlCfg::correct(SliceEndKind::First, 4);
        let mut nodes = fl_emit(&cfg);
        nodes.pop(); // drop the trailing Store
        assert!(
            fold_emitted_slice_first_last(&nodes).is_none(),
            "a first/last without a niche store must be out of the fold slice"
        );
    }

    // =======================================================================
    // Lane 7: `Range::next` STATE TRANSITION (the `Load -> pre-state symbol`
    // primitive). The emitter hand-builds the EXACT shape `lower_range_next`
    // emits (the offset-0 `start` load shortcut, the stride-1 `iter_field_addr`
    // chain for `end` — NO `Mul`, `emit_element_addr`'s `size == 1` identity
    // skip — the `ICmp`, the `+1` `Add`, the two `Select`s, and the three typed
    // `Store`s incl. `store_option_some_value`'s Direct arm), so the fold's
    // reconstruction is exercised against the spec end to end.
    // =======================================================================
    const RN_SELF: ValueId = ValueId::new(90);
    const RN_DEST: ValueId = ValueId::new(91);
    /// Option<i64/u64>: Some=1 / None=0, tag at slot offset 0, payload at 8.
    const RN_SOME: i128 = 1;
    const RN_NONE: i128 = 0;
    const RN_TAG_OFF: u64 = 0;
    const RN_PAYLOAD_OFF: u64 = 8;

    #[derive(Clone)]
    struct RnCfg {
        /// The SPEC-side signedness the discharge asserts (the index type's).
        signed: bool,
        /// The EMITTED comparison (`Slt` correct for signed, `Ult` for unsigned).
        cmp_op: ICmpOp,
        /// The `Add` step constant (`1` = correct).
        step: i128,
        /// `ICmp(start, end)` operand order (`false` = swapped `ICmp(end, start)`).
        cmp_start_end: bool,
        /// `Select(cond, advanced, start)` arm order (`false` = advance-when-done).
        advance_in_range: bool,
        /// Payload stores the PRE-state `start` (`false` = post-increment yield).
        payload_is_start: bool,
        /// Tag `Select(cond, some, none)` arm order (`false` = swapped).
        tag_some_in_range: bool,
        /// Byte offset of the state write-back within the SELF slot (`0` = correct;
        /// `8` clobbers `end` instead).
        writeback_off: u64,
        /// Emit the state write-back store at all (`false` = dropped write-back).
        emit_writeback: bool,
        /// The element trust-ir type (`I64` = the supported 64-bit lane).
        elem_ty: TrustIrTy,
        /// The tag pipeline type (consts / `Select` / tag `Store`). The REAL
        /// emission uses the layout tag scalar — `I8` for `Option<i64>`'s 1-byte
        /// tag; `rn_obligations` derives `tag_width` from this type.
        tag_ty: TrustIrTy,
        /// The state write-back `Store` type (`I64` = correct; `I32` = the
        /// TRUNCATING write-back of adversarial-review defect 2).
        writeback_ty: TrustIrTy,
        /// Defect-1 shape: the payload RELOADS `(self, 0)` AFTER the write-back
        /// store (the post-increment-yield-via-reload emission) instead of using
        /// the pre-state `start`. The fold must bail (load-after-store).
        payload_reloads_state: bool,
        /// Byte offset the `end` load reads from within the SELF slot. The REAL
        /// emission loads `end` at the ELEMENT size (`elem_size()`); a different
        /// offset is the lane-13 "end-offset lie" (names a different pre-state
        /// symbol than the spec -> REFUTED).
        end_load_off: u64,
        /// Byte offset of the `Option` payload cell in the dest slot (the real
        /// layouts put it at the element size for narrow `Option<T>`: tag at 0,
        /// payload right after).
        payload_off: u64,
        /// Lane-13 open-question shape: the advance is computed at I64 (`Add`
        /// `I64` directly over the narrow loads) and the `new_start` `Select`
        /// runs at I64, while the write-back `Store` stays at the NARROW
        /// element type (which truncates to exactly the machine bytes).
        add_at_i64: bool,
    }

    impl RnCfg {
        fn correct(signed: bool) -> Self {
            Self {
                signed,
                cmp_op: if signed { ICmpOp::Slt } else { ICmpOp::Ult },
                step: 1,
                cmp_start_end: true,
                advance_in_range: true,
                payload_is_start: true,
                tag_some_in_range: true,
                writeback_off: 0,
                emit_writeback: true,
                elem_ty: TrustIrTy::I64,
                tag_ty: TrustIrTy::I64,
                writeback_ty: TrustIrTy::I64,
                payload_reloads_state: false,
                end_load_off: 8,
                payload_off: RN_PAYLOAD_OFF,
                add_at_i64: false,
            }
        }

        /// A correct NARROW-element emission (lane 13): everything runs at
        /// `elem_ty` — loads, compare, `+1`, `Select`, write-back and payload
        /// stores — and the layout mirrors the real `Option<T>` for narrow `T`
        /// (tag scalar of the element width at offset 0, payload right after).
        fn correct_w(signed: bool, elem_ty: TrustIrTy) -> Self {
            let w = u64::from(scalar_byte_width(&elem_ty).expect("scalar elem ty"));
            Self {
                elem_ty: elem_ty.clone(),
                tag_ty: elem_ty.clone(),
                writeback_ty: elem_ty,
                end_load_off: w,
                payload_off: w,
                ..Self::correct(signed)
            }
        }

        fn elem_size(&self) -> u64 {
            u64::from(scalar_byte_width(&self.elem_ty).expect("scalar elem ty"))
        }
    }

    /// The `iter_field_addr(base, off)` chain for `off != 0`: `Const off` +
    /// `emit_element_addr(base, off, /*size=*/1)` = `Copy(Ptr)` / `PtrToInt` /
    /// `Copy(I64)` / `Add` / `IntToPtr` — stride 1, so NO `Mul` (the
    /// `size == 1` identity skip in `emit_element_addr`).
    fn rn_field_addr(
        nodes: &mut Vec<InstrNode>,
        next: &mut u32,
        base: ValueId,
        off: i128,
    ) -> ValueId {
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        let idx = fresh(next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(off),
            },
            idx,
        ));
        let bp = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::Ptr,
                operand: base,
            },
            bp,
        ));
        let bi = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: bp,
            },
            bi,
        ));
        let i64v = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::I64,
                operand: idx,
            },
            i64v,
        ));
        let ai = fresh(next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: bi,
                rhs: i64v,
            })
            .with_result(ai),
        );
        let p = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: ai,
            },
            p,
        ));
        p
    }

    fn rn_emit(cfg: &RnCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 100u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. start = Load(elem_ty, RN_SELF)  (`iter_field_addr` offset-0 shortcut:
        //    the start address IS the self slot pointer).
        let start = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: cfg.elem_ty.clone(),
                ptr: RN_SELF,
                volatile: false,
                align: None,
            },
            start,
        ));
        // 2. end_addr = iter_field_addr(RN_SELF, end_load_off — the element
        //    size in the real emission); 3. end = Load.
        let end_addr = rn_field_addr(&mut nodes, &mut next, RN_SELF, cfg.end_load_off as i128);
        let end = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: cfg.elem_ty.clone(),
                ptr: end_addr,
                volatile: false,
                align: None,
            },
            end,
        ));
        // 4. cond = ICmp(op, start, end)  (or swapped operands).
        let (cl, cr) = if cfg.cmp_start_end {
            (start, end)
        } else {
            (end, start)
        };
        let cond = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: cfg.cmp_op,
                ty: cfg.elem_ty.clone(),
                lhs: cl,
                rhs: cr,
            })
            .with_result(cond),
        );
        // 5. one = Const step; advanced = Add(start, one). The lane-13
        //    open-question shape (`add_at_i64`) computes the advance AT I64
        //    over the narrow loads (and Selects at I64) while the write-back
        //    store below stays narrow.
        let arith_ty = if cfg.add_at_i64 {
            TrustIrTy::I64
        } else {
            cfg.elem_ty.clone()
        };
        let one = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: arith_ty.clone(),
                value: Constant::Int(cfg.step),
            },
            one,
        ));
        let advanced = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: arith_ty.clone(),
                lhs: start,
                rhs: one,
            })
            .with_result(advanced),
        );
        // 6. new_start = Select(cond, advanced, start)  (or arms swapped).
        let (tv, ev) = if cfg.advance_in_range {
            (advanced, start)
        } else {
            (start, advanced)
        };
        let new_start = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: arith_ty,
                cond,
                then_val: tv,
                else_val: ev,
            })
            .with_result(new_start),
        );
        // 7. Store(writeback_ty, self + writeback_off, new_start) — the STATE
        //    WRITE-BACK (offset 0 reuses the slot pointer; offset 8 reuses the
        //    end address; a non-I64 `writeback_ty` models the TRUNCATING store
        //    of adversarial-review defect 2).
        if cfg.emit_writeback {
            let wb_ptr = if cfg.writeback_off == 0 {
                RN_SELF
            } else {
                assert_eq!(
                    cfg.writeback_off, cfg.end_load_off,
                    "test shape only models 0/end"
                );
                end_addr
            };
            nodes.push(InstrNode::new(Inst::Store {
                ty: cfg.writeback_ty.clone(),
                ptr: wb_ptr,
                value: new_start,
                volatile: false,
                align: None,
            }));
        }
        // 8. `store_option_some_value` Direct arm: some/none tag consts, the tag
        //    `Select`, the tag store at (dest, 0) (offset-0 shortcut), and the
        //    payload store at (dest, 8). The tag pipeline runs at `tag_ty` (the
        //    REAL emission uses the 1-byte layout tag scalar for `Option<i64>`).
        let some_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: cfg.tag_ty.clone(),
                value: Constant::Int(RN_SOME),
            },
            some_tag,
        ));
        let none_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: cfg.tag_ty.clone(),
                value: Constant::Int(RN_NONE),
            },
            none_tag,
        ));
        let (ttv, tev) = if cfg.tag_some_in_range {
            (some_tag, none_tag)
        } else {
            (none_tag, some_tag)
        };
        let chosen_tag = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: cfg.tag_ty.clone(),
                cond,
                then_val: ttv,
                else_val: tev,
            })
            .with_result(chosen_tag),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: cfg.tag_ty.clone(),
            ptr: RN_DEST,
            value: chosen_tag,
            volatile: false,
            align: None,
        }));
        let payload_addr = rn_field_addr(&mut nodes, &mut next, RN_DEST, cfg.payload_off as i128);
        // Defect-1 shape: RELOAD the just-written `(self, 0)` cell and yield THAT
        // (the machine yields `start + 1`; the fold must bail on load-after-store,
        // never bind the reload to the pre-state symbol).
        let payload = if cfg.payload_reloads_state {
            let reloaded = fresh(&mut next);
            nodes.push(node(
                Inst::Load {
                    ty: cfg.elem_ty.clone(),
                    ptr: RN_SELF,
                    volatile: false,
                    align: None,
                },
                reloaded,
            ));
            reloaded
        } else if cfg.payload_is_start {
            start
        } else {
            new_start
        };
        nodes.push(InstrNode::new(Inst::Store {
            ty: cfg.elem_ty.clone(),
            ptr: payload_addr,
            value: payload,
            volatile: false,
            align: None,
        }));
        nodes
    }

    fn rn_obligations(name: &str, cfg: &RnCfg) -> Option<Vec<ProofObligation>> {
        let folded = fold_emitted_range_next(&rn_emit(cfg)).expect("Range::next in slice");
        // The LAYOUT-designated tag width is the emitted tag type's width here —
        // the capture site derives it from the real layout's `tag.ty` the same way.
        let tag_width = scalar_byte_width(&cfg.tag_ty).expect("scalar tag ty");
        range_next_obligations(
            name,
            &folded,
            cfg.signed,
            RN_SELF,
            RN_DEST,
            cfg.elem_size(),
            RN_TAG_OFF,
            tag_width,
            cfg.payload_off,
            RN_SOME as u64,
            RN_NONE as u64,
        )
    }

    fn rn_discharge(name: &str, cfg: &RnCfg) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations = rn_obligations(name, cfg).expect("Range::next obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the three stored values as EXACTLY the spec formulas
    /// (over the same pre-state load symbols) for a correct signed emission.
    #[test]
    fn fold_reconstructs_range_next() {
        let cfg = RnCfg::correct(true);
        let folded = fold_emitted_range_next(&rn_emit(&cfg)).expect("in slice");
        let spec = range_next_spec(
            true,
            &ld_value_name(RN_SELF, 0),
            &ld_value_name(RN_SELF, 8),
            RN_SOME as u64,
            RN_NONE as u64,
        );
        assert_eq!(folded.store_value(RN_SELF, 0).unwrap(), spec.new_start);
        assert_eq!(folded.store_value(RN_DEST, RN_TAG_OFF).unwrap(), spec.tag);
        assert_eq!(
            folded.store_value(RN_DEST, RN_PAYLOAD_OFF).unwrap(),
            spec.payload
        );
    }

    /// POSITIVE: a correct SIGNED `Range::next` (`Slt`) is NOT refuted.
    #[test]
    fn correct_signed_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_signed", &RnCfg::correct(true));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct signed Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct UNSIGNED `Range::next` (`Ult`) is NOT refuted.
    #[test]
    fn correct_unsigned_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_unsigned", &RnCfg::correct(false));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct unsigned Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY (a): SIGNEDNESS CONFUSION — the bridge emits an UNSIGNED
    /// `Ult` for a SIGNED range. The folded cond is `start <u end` where the spec
    /// has `start <s end` (they differ e.g. on `start = -1, end = 0`) -> REFUTED.
    #[test]
    fn flipped_signedness_range_next_is_refuted() {
        let cfg = RnCfg {
            cmp_op: ICmpOp::Ult,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_signedness", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a signedness-confused comparison must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (b): ADVANCE-WHEN-DONE — the `new_start` `Select` arms are
    /// swapped (`cond ? start : advanced`), so a FINISHED range keeps advancing
    /// past its end (and an in-range one never advances: an infinite loop) ->
    /// REFUTED.
    #[test]
    fn advance_when_done_range_next_is_refuted() {
        let cfg = RnCfg {
            advance_in_range: false,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_advance_done", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped new_start Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (c): STEP = 2 — the advance adds `2` instead of `1`, so the
    /// iterator skips every other element -> REFUTED.
    #[test]
    fn step_two_range_next_is_refuted() {
        let cfg = RnCfg {
            step: 2,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_step2", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a step of 2 must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (d): POST-INCREMENT YIELD — the payload stores `new_start`
    /// instead of the PRE-state `start`, so every yielded value is off by one ->
    /// REFUTED.
    #[test]
    fn post_increment_payload_range_next_is_refuted() {
        let cfg = RnCfg {
            payload_is_start: false,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a post-increment payload must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (e): TAG ARMS SWAPPED — the tag `Select` yields `None` on
    /// an in-range element (and `Some` on exhaustion) -> REFUTED.
    #[test]
    fn swapped_tag_arms_range_next_is_refuted() {
        let cfg = RnCfg {
            tag_some_in_range: false,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_tag_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped tag Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (f): SWAPPED LOADS — the comparison is `ICmp(end, start)`.
    /// The folded cond is `end <s start` where the spec has `start <s end` ->
    /// REFUTED.
    #[test]
    fn swapped_start_end_loads_range_next_is_refuted() {
        let cfg = RnCfg {
            cmp_start_end: false,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_swap_loads", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped start/end comparison must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK (g): the state write-back targets the END offset `(self, 8)`
    /// instead of `(self, 0)` — an `end`-clobbering store. The store set is not
    /// the exact expected three cells -> obligations `None` (skip, sound).
    #[test]
    fn writeback_to_end_offset_range_next_is_out_of_shape() {
        let cfg = RnCfg {
            writeback_off: 8,
            ..RnCfg::correct(true)
        };
        assert!(
            rn_obligations("rn_wb_end", &cfg).is_none(),
            "a write-back to the end offset must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK (h): the state write-back is DROPPED entirely (no self store).
    /// Only two stores fold -> obligations `None` (skip, sound — never a
    /// spurious Refined over a missing state transition).
    #[test]
    fn dropped_writeback_range_next_is_out_of_shape() {
        let cfg = RnCfg {
            emit_writeback: false,
            ..RnCfg::correct(true)
        };
        assert!(
            rn_obligations("rn_no_wb", &cfg).is_none(),
            "a dropped state write-back must fail the exact-store-set shape check"
        );
    }

    // =======================================================================
    // Lane 13: NARROW-element `Range::next` (i8..u32) — the width-faithful
    // generalization of the lane-7 machinery. The narrow loads bind MASKED
    // width-tagged symbols, the narrow Add wraps at width, the narrow signed
    // ICmp sign-extends (all modeling trust-ir `interpret.rs`), the narrow
    // Select folds masked runtime arms, and the obligations compare each
    // store AT ITS WIDTH against `range_next_spec_w`.
    // =======================================================================

    /// LANE 13 (replaces the lane-10 out-of-slice gate test): a 4-byte
    /// (`I32`) element now FOLDS, and the folded stores reconstruct EXACTLY
    /// the width-faithful spec formulas over the same masked width-tagged
    /// pre-state symbols.
    #[test]
    fn narrow_fold_reconstructs_range_next_w4() {
        let cfg = RnCfg::correct_w(true, TrustIrTy::I32);
        let folded =
            fold_emitted_range_next(&rn_emit(&cfg)).expect("narrow Range::next in slice");
        let spec = range_next_spec_w(
            true,
            4,
            &ld_value_name_w(RN_SELF, 0, 4),
            &ld_value_name_w(RN_SELF, 4, 4),
            RN_SOME as u64,
            RN_NONE as u64,
            4,
        );
        assert_eq!(folded.store_value(RN_SELF, 0).unwrap(), spec.new_start);
        assert_eq!(folded.store_value(RN_DEST, RN_TAG_OFF).unwrap(), spec.tag);
        assert_eq!(folded.store_value(RN_DEST, 4).unwrap(), spec.payload);
    }

    /// POSITIVE: a correct SIGNED i32 `Range::next` (`Slt` at `I32`) is NOT
    /// refuted (Refined when a solver is available).
    #[test]
    fn correct_i32_signed_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_i32_signed", &RnCfg::correct_w(true, TrustIrTy::I32));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct signed i32 Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct UNSIGNED u32 `Range::next` (`Ult` at `U32`) is NOT
    /// refuted.
    #[test]
    fn correct_u32_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_u32", &RnCfg::correct_w(false, TrustIrTy::U32));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct u32 Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct SIGNED i8 `Range::next` (1-byte element — the
    /// tightest wrap/sign band) is NOT refuted.
    #[test]
    fn correct_i8_signed_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_i8_signed", &RnCfg::correct_w(true, TrustIrTy::I8));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct signed i8 Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct UNSIGNED u16 `Range::next` (2-byte element) is NOT
    /// refuted.
    #[test]
    fn correct_u16_range_next_is_not_refuted() {
        let outcome = rn_discharge("rn_u16", &RnCfg::correct_w(false, TrustIrTy::U16));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct u16 Range::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY (lane 13, the classic): SIGNEDNESS CONFUSION at i32 —
    /// the bridge emits an UNSIGNED `Ult` for a SIGNED i32 range. The folded
    /// cond compares the MASKED values unsigned where the spec SIGN-EXTENDS
    /// (they differ e.g. on `start = -1 (0xFFFF_FFFF), end = 0`) -> REFUTED.
    #[test]
    fn narrow_flipped_signedness_range_next_is_refuted() {
        let cfg = RnCfg {
            cmp_op: ICmpOp::Ult,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_signedness", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a signedness-confused i32 comparison must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (lane 13): END-OFFSET LIE — the `end` load reads offset
    /// 8 where a 4-byte element's `end` lives at offset 4. The fold binds the
    /// WRONG width-tagged pre-state symbol (`ld_v.._o8_w4`) while the spec is
    /// over `ld_v.._o4_w4` — genuinely different formulas -> REFUTED.
    #[test]
    fn narrow_end_offset_lie_range_next_is_refuted() {
        let cfg = RnCfg {
            end_load_off: 8,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_end_lie", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an i32 end loaded from offset != 4 must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (lane 13): ADVANCE-WHEN-DONE at i32 — the `new_start`
    /// `Select` arms are swapped -> REFUTED.
    #[test]
    fn narrow_advance_when_done_range_next_is_refuted() {
        let cfg = RnCfg {
            advance_in_range: false,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_advance_done", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped narrow new_start Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (lane 13): POST-INCREMENT YIELD at i32 — the payload
    /// stores `new_start` instead of the PRE-state `start` -> REFUTED.
    #[test]
    fn narrow_post_increment_payload_range_next_is_refuted() {
        let cfg = RnCfg {
            payload_is_start: false,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a narrow post-increment payload must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (lane 13): TAG ARMS SWAPPED at i32 -> REFUTED.
    #[test]
    fn narrow_swapped_tag_arms_range_next_is_refuted() {
        let cfg = RnCfg {
            tag_some_in_range: false,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_tag_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped narrow tag Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// LANE-13 WRAP-BUG SHAPE (the spec's "new_start unmasked" hazard): a
    /// narrow (i32) element whose state write-back stores 8 BYTES — the
    /// unmasked 64-bit `new_start` written over `start` AND `end` (an i8/i32
    /// range near its type max would never wrap back, and `end` is
    /// clobbered). The width-exact store shape check rejects it -> obligations
    /// `None` (shape fail, skip — sound, and the drain trace makes it
    /// visible). This is the OLD `narrow_element_range_next_is_out_of_slice`
    /// cfg (narrow loads, I64 write-back), now caught by WIDTH not by an
    /// out-of-slice bail.
    #[test]
    fn narrow_elem_wide_writeback_is_out_of_shape() {
        let cfg = RnCfg {
            writeback_ty: TrustIrTy::I64,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        assert!(
            rn_obligations("rn_w4_wide_wb", &cfg).is_none(),
            "an 8-byte write-back of a 4-byte element must fail the width-exact shape check"
        );
    }

    /// LANE-13 OPEN QUESTION (worked out, encoded as reality): an emission
    /// that computes the advance AT I64 over the narrow loads (`Add I64`,
    /// `Select I64`) but stores the result through the NARROW 4-byte
    /// write-back. VERDICT: it neither refutes nor shape-fails — it is
    /// REFINED, and that is the CORRECT verdict: the machine's 4-byte store
    /// writes exactly the low 4 bytes (`interpret.rs::eval_store` writes
    /// `byte_size(ty)` bytes), and the low 32 bits of a 64-bit `s + 1` equal
    /// the 32-bit wrapped `(s + 1) & mask` for every `s` — the width-masked
    /// obligation (`bvand` both sides) models exactly the machine's
    /// observable bytes, so the wrap case (`s = 0xFFFF_FFFF` -> stored `0`)
    /// agrees on both sides. The store shape check still passes because the
    /// STORE is at the expected 4-byte width; only a WIDE store (the test
    /// above) is a width lie.
    #[test]
    fn narrow_i64_add_with_narrow_store_is_refined() {
        let cfg = RnCfg {
            add_at_i64: true,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_i64_add", &cfg);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a 64-bit advance truncated by the narrow store is machine-correct \
             and must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// LANE-13 OPEN QUESTION, companion shape: the WELL-TYPED variant of the
    /// 64-bit-advance emission would `ZExt` the narrow loads to I64 first —
    /// but `fold_emitted_range_next` has NO ZExt arm (the real narrow
    /// emission never casts; the lane-11 ZExt/Trunc arms live in the StepBy
    /// fold only), so that shape leaves the fold slice entirely -> fold
    /// `None` (skip, sound — never a guessed verdict).
    #[test]
    fn narrow_zext_advance_shape_is_out_of_slice() {
        let cfg = RnCfg::correct_w(true, TrustIrTy::I32);
        let mut nodes = rn_emit(&cfg);
        // Splice a ZExt(I32 -> I64) of the start load in front (result unused
        // — its mere presence is out of slice).
        let zext = InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: TrustIrTy::I32,
            dst_ty: TrustIrTy::I64,
            operand: ValueId::new(100), // the start load's result id in rn_emit
        })
        .with_result(ValueId::new(9999));
        nodes.insert(1, zext);
        assert!(
            fold_emitted_range_next(&nodes).is_none(),
            "a ZExt in the captured Range::next slice must bail the fold"
        );
    }

    /// LANE-13 SANITY: the i32 signed refutation of the WRAP semantics — a
    /// `step` of 2 at i32 (skips every other element, and its wrap differs)
    /// is REFUTED, confirming the masked add is not vacuous.
    #[test]
    fn narrow_step_two_range_next_is_refuted() {
        let cfg = RnCfg {
            step: 2,
            ..RnCfg::correct_w(true, TrustIrTy::I32)
        };
        let outcome = rn_discharge("rn_w4_step2", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a narrow step of 2 must be REFUTED, got {outcome:?}"
        );
    }

    /// LANE-13 REGRESSION GUARD: the 64-bit v1 path is BYTE-IDENTICAL — the
    /// folded v1 stores still reconstruct EXACTLY the UNCHANGED
    /// `range_next_spec` formulas over the UNMASKED `ld_value_name` symbols
    /// (no `_w` suffix, no masks — the narrow generalization must not have
    /// perturbed the landed lane-7 fold output).
    #[test]
    fn v1_fold_output_is_unchanged_by_lane13() {
        let cfg = RnCfg::correct(true);
        let folded = fold_emitted_range_next(&rn_emit(&cfg)).expect("in slice");
        let spec = range_next_spec(
            true,
            &ld_value_name(RN_SELF, 0),
            &ld_value_name(RN_SELF, 8),
            RN_SOME as u64,
            RN_NONE as u64,
        );
        assert_eq!(folded.store_value(RN_SELF, 0).unwrap(), spec.new_start);
        assert_eq!(folded.store_value(RN_DEST, RN_TAG_OFF).unwrap(), spec.tag);
        assert_eq!(
            folded.store_value(RN_DEST, RN_PAYLOAD_OFF).unwrap(),
            spec.payload
        );
        // And the width-tagged narrow symbols are entirely absent.
        assert!(
            folded.inputs.iter().all(|(n, _)| !n.contains("_w")),
            "the 64-bit fold must not name width-tagged symbols: {:?}",
            folded.inputs
        );
    }

    /// REAL-EMISSION FIDELITY (adversarial-review note): the actual layout tag
    /// scalar for `Option<i64>` is 1 BYTE (`I8`). A correct emission with the
    /// 1-byte tag pipeline + `tag_width == 1` must NOT refute.
    #[test]
    fn real_narrow_i8_tag_range_next_is_not_refuted() {
        let cfg = RnCfg {
            tag_ty: TrustIrTy::I8,
            ..RnCfg::correct(true)
        };
        let outcome = rn_discharge("rn_i8_tag", &cfg);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct 1-byte-tag emission must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// DEFECT-1 REGRESSION (CONFIRMED-by-probe false Refined, now closed): the
    /// payload RELOADS the just-written `(self, 0)` cell after the write-back —
    /// the machine yields `start + 1` (the post-increment bug via reload). The
    /// fold must BAIL on the load-after-store, never bind the reload to the
    /// pre-state symbol.
    #[test]
    fn reload_after_writeback_payload_is_out_of_slice() {
        let cfg = RnCfg {
            payload_reloads_state: true,
            ..RnCfg::correct(true)
        };
        assert!(
            fold_emitted_range_next(&rn_emit(&cfg)).is_none(),
            "a payload reloading the written-back state cell must be out of slice \
             (load-after-store binds no pre-state symbol)"
        );
    }

    /// DEFECT-2 REGRESSION (unchecked store width): a TRUNCATING 4-byte state
    /// write-back (`Store I32`) folds to the full 64-bit formula but writes only
    /// half the cell (wraps `start` at 2^32 -> an infinite iterator). The
    /// obligations' width-checked shape check must reject it.
    #[test]
    fn narrow_writeback_store_is_out_of_shape() {
        let cfg = RnCfg {
            writeback_ty: TrustIrTy::I32,
            ..RnCfg::correct(true)
        };
        assert!(
            rn_obligations("rn_narrow_wb", &cfg).is_none(),
            "a 4-byte state write-back must fail the width-checked shape check"
        );
    }

    /// DEFECT-4 REGRESSION (degenerate expected cells): if the layout ever made
    /// `tag_off == payload_off`, one emitted store could satisfy BOTH
    /// expectations and a third store would go unvalidated. The pairwise-distinct
    /// check must return `None`.
    #[test]
    fn degenerate_equal_option_offsets_is_out_of_shape() {
        let cfg = RnCfg::correct(true);
        let folded = fold_emitted_range_next(&rn_emit(&cfg)).expect("Range::next in slice");
        assert!(
            range_next_obligations(
                "rn_degenerate",
                &folded,
                cfg.signed,
                RN_SELF,
                RN_DEST,
                8,
                RN_PAYLOAD_OFF, // tag_off == payload_off: degenerate
                8,
                RN_PAYLOAD_OFF,
                RN_SOME as u64,
                RN_NONE as u64,
            )
            .is_none(),
            "non-distinct expected cells must fail the pairwise-distinct check"
        );
    }

    // =======================================================================
    // Lane 6: `<[T]>::split_first`/`split_last` niche-`Option<(&T, &[T])>`.
    // The emitter hand-builds the EXACT shape `lower_slice_split_first_last` +
    // `store_option_some_value`'s RefAndSlice arm emit (the emptiness `ICmp
    // Ne(len, 0)`, the `Sub(len, 1)`, `emit_element_addr` with the `size == 1`
    // Mul-skip, the `None` `Const`+`IntToPtr`, the UNCONDITIONAL tail-len store
    // FIRST, then the niche `Select` store + the plain other-pointer store —
    // incl. `iter_field_addr`'s offset-0 shortcut at `f0 == 0`). Offsets mirror
    // the REAL probed layout of `Option<(&i64, &[i64])>`: declaration order,
    // `f0 = 0` (the `&T` — THE LAYOUT-DESIGNATED NICHE), `f1 = 8` (tail data),
    // `f1 + 8 = 16` (tail len). The harness also emits the `f1`-niche mirror
    // shape so BOTH layout positions are exercised.
    // =======================================================================
    const SE_DATA: ValueId = ValueId::new(90);
    const SE_LEN: ValueId = ValueId::new(91);
    const SE_DEST: ValueId = ValueId::new(92);
    const SE_WRONGBASE: ValueId = ValueId::new(93);
    /// The probed `Option<(&i64, &[i64])>` layout: `&T` at 0, tail data at 8.
    const SE_F0: u64 = 0;
    const SE_F1: u64 = 8;

    #[derive(Clone)]
    struct SeCfg {
        kind: SliceEndKind,
        /// The LAYOUT-designated niche position the OBLIGATIONS assert (the
        /// keystone input — from the capture's `tag.offset == f0`, never the
        /// emission).
        niche_at_f0: bool,
        /// The emptiness comparison (`Ne` = correct `len != 0`).
        cond_op: ICmpOp,
        /// The `None` niche integer (`0` = correct null).
        none_val: i128,
        /// `Last` only: index the head at `len-1` (`true` = correct; `false`
        /// indexes `len` — one past the end).
        last_minus_one: bool,
        /// The element-address `Mul` constant (= `elem_size` correct; `1` takes
        /// `emit_element_addr`'s identity Mul-skip).
        scale: i128,
        /// The base the element pointers are computed from (`SE_DATA` = correct).
        base: ValueId,
        /// Store the raw pointer into the niche cell WITHOUT a `Select` (the
        /// dropped-`Select` KEYSTONE defect: an empty slice decodes `Some`).
        dropped_select: bool,
        /// `tail_len = Sub(len, one)` (`true` = correct; `false` = the swapped
        /// `Sub(one, len)`).
        tail_len_sub_len_one: bool,
        /// Emit the unconditional tail-length store at all (`false` = dropped).
        emit_tail_len: bool,
        /// The EMITTED niche-`Select` position (`None` = follow `niche_at_f0`;
        /// `Some(false)` with `niche_at_f0 == true` = the SELECT-ON-WRONG-FIELD
        /// defect: the `Select` flows into `f1` while the LAYOUT designated `f0`).
        select_at_f0: Option<bool>,
        /// Emit a spurious 4th store (the shape check must reject).
        extra_store: bool,
        /// The niche-cell store type (`Ptr` = the correct 8 bytes; `I32` = the
        /// TRUNCATING narrow store the width check must reject).
        niche_store_ty: TrustIrTy,
    }

    impl SeCfg {
        fn correct(kind: SliceEndKind, niche_at_f0: bool, scale: i128) -> Self {
            Self {
                kind,
                niche_at_f0,
                cond_op: ICmpOp::Ne,
                none_val: 0,
                last_minus_one: true,
                scale,
                base: SE_DATA,
                dropped_select: false,
                tail_len_sub_len_one: true,
                emit_tail_len: true,
                select_at_f0: None,
                extra_store: false,
                niche_store_ty: TrustIrTy::Ptr,
            }
        }
    }

    /// `emit_element_addr(base, idx, scale)`: `Copy(Ptr)` / `PtrToInt` /
    /// `Copy(I64)` (the index coerce) / [`Const scale` + `Mul` unless
    /// `scale == 1` — the identity Mul-skip] / `Add` / `IntToPtr`.
    fn se_element_addr(
        nodes: &mut Vec<InstrNode>,
        next: &mut u32,
        base: ValueId,
        idx: ValueId,
        scale: i128,
    ) -> ValueId {
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        let bp = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::Ptr,
                operand: base,
            },
            bp,
        ));
        let bi = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: bp,
            },
            bi,
        ));
        let i64v = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::I64,
                operand: idx,
            },
            i64v,
        ));
        let offset = if scale == 1 {
            i64v
        } else {
            let stride = fresh(next);
            nodes.push(node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(scale),
                },
                stride,
            ));
            let offv = fresh(next);
            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: TrustIrBinOp::Mul,
                    ty: TrustIrTy::I64,
                    lhs: i64v,
                    rhs: stride,
                })
                .with_result(offv),
            );
            offv
        };
        let ai = fresh(next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: bi,
                rhs: offset,
            })
            .with_result(ai),
        );
        let p = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: ai,
            },
            p,
        ));
        p
    }

    fn se_emit(cfg: &SeCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 100u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. zero = const 0; cond = ICmp <op>(len, zero).
        let zero = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0),
            },
            zero,
        ));
        let cond = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: cfg.cond_op,
                ty: TrustIrTy::I64,
                lhs: SE_LEN,
                rhs: zero,
            })
            .with_result(cond),
        );
        // 2. one = const 1; tail_len = Sub(len, one)  (or the swapped Sub).
        let one = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(1),
            },
            one,
        ));
        let (sl, sr) = if cfg.tail_len_sub_len_one {
            (SE_LEN, one)
        } else {
            (one, SE_LEN)
        };
        let tail_len = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty: TrustIrTy::I64,
                lhs: sl,
                rhs: sr,
            })
            .with_result(tail_len),
        );
        // 3. Kind-dependent element addresses.
        let (first_ptr, tail_data) = match cfg.kind {
            SliceEndKind::First => {
                let td = se_element_addr(&mut nodes, &mut next, cfg.base, one, cfg.scale);
                (cfg.base, td)
            }
            SliceEndKind::Last => {
                let idx = if cfg.last_minus_one { tail_len } else { SE_LEN };
                let fp = se_element_addr(&mut nodes, &mut next, cfg.base, idx, cfg.scale);
                (fp, cfg.base)
            }
        };
        // 4. The RefAndSlice arm: none const + IntToPtr, the UNCONDITIONAL tail
        //    len store FIRST, then the niche Select store + the plain other store.
        let none_int = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(cfg.none_val),
            },
            none_int,
        ));
        let none_ptr = fresh(&mut next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: none_int,
            },
            none_ptr,
        ));
        if cfg.emit_tail_len {
            let len_addr = rn_field_addr(&mut nodes, &mut next, SE_DEST, (SE_F1 + 8) as i128);
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::I64,
                ptr: len_addr,
                value: tail_len,
                volatile: false,
                align: None,
            }));
        }
        // The EMITTED Select position (for the SELECT-ON-WRONG-FIELD defect it
        // deliberately disagrees with the obligations' layout `niche_at_f0`).
        let emitted_at_f0 = cfg.select_at_f0.unwrap_or(cfg.niche_at_f0);
        let select_into = |nodes: &mut Vec<InstrNode>, next: &mut u32, ptr: ValueId| {
            if cfg.dropped_select {
                ptr
            } else {
                let fresh = |next: &mut u32| {
                    let v = ValueId::new(*next);
                    *next += 1;
                    v
                };
                let ch = fresh(next);
                nodes.push(
                    InstrNode::new(Inst::Select {
                        ty: TrustIrTy::Ptr,
                        cond,
                        then_val: ptr,
                        else_val: none_ptr,
                    })
                    .with_result(ch),
                );
                ch
            }
        };
        if emitted_at_f0 {
            let chosen = select_into(&mut nodes, &mut next, first_ptr);
            // f0 == 0: `iter_field_addr`'s offset-0 shortcut — the slot pointer.
            nodes.push(InstrNode::new(Inst::Store {
                ty: cfg.niche_store_ty.clone(),
                ptr: SE_DEST,
                value: chosen,
                volatile: false,
                align: None,
            }));
            let data_addr = rn_field_addr(&mut nodes, &mut next, SE_DEST, SE_F1 as i128);
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::Ptr,
                ptr: data_addr,
                value: tail_data,
                volatile: false,
                align: None,
            }));
        } else {
            let chosen = select_into(&mut nodes, &mut next, tail_data);
            let niche_addr = rn_field_addr(&mut nodes, &mut next, SE_DEST, SE_F1 as i128);
            nodes.push(InstrNode::new(Inst::Store {
                ty: cfg.niche_store_ty.clone(),
                ptr: niche_addr,
                value: chosen,
                volatile: false,
                align: None,
            }));
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::Ptr,
                ptr: SE_DEST,
                value: first_ptr,
                volatile: false,
                align: None,
            }));
        }
        if cfg.extra_store {
            let extra_addr = rn_field_addr(&mut nodes, &mut next, SE_DEST, 24);
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::Ptr,
                ptr: extra_addr,
                value: none_ptr,
                volatile: false,
                align: None,
            }));
        }
        nodes
    }

    fn se_obligations(name: &str, cfg: &SeCfg, elem_size: u64) -> Option<Vec<ProofObligation>> {
        let folded = fold_emitted_split_ends(&se_emit(cfg)).expect("split ends in slice");
        split_ends_obligations(
            name,
            &folded,
            cfg.kind,
            cfg.niche_at_f0,
            SE_DEST,
            SE_F0,
            SE_F1,
            SE_DATA,
            SE_LEN,
            elem_size,
        )
    }

    fn se_discharge(name: &str, cfg: &SeCfg, elem_size: u64) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations = se_obligations(name, cfg, elem_size).expect("split ends obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the two pointer cells as EXACTLY the spec formulas
    /// (over the same `data`/`len` symbols) for a correct `split_first` with the
    /// layout niche at `f0`. (`tail_len` folds to the wrapping-equivalent
    /// `len + (-1)` and is checked semantically by the discharge tests.)
    #[test]
    fn fold_reconstructs_split_first() {
        let cfg = SeCfg::correct(SliceEndKind::First, true, 8);
        let folded = fold_emitted_split_ends(&se_emit(&cfg)).expect("in slice");
        let spec = split_first_last_spec(
            SliceEndKind::First,
            true,
            &sa_value_name(SE_DATA),
            &sa_value_name(SE_LEN),
            8,
        );
        assert_eq!(folded.store_value(SE_DEST, SE_F0).unwrap(), spec.f0);
        assert_eq!(folded.store_value(SE_DEST, SE_F1).unwrap(), spec.f1);
    }

    /// POSITIVE: a correct `split_first` (niche at `f0` — the REAL probed
    /// `Option<(&i64, &[i64])>` position) is NOT refuted.
    #[test]
    fn correct_split_first_is_not_refuted() {
        let outcome = se_discharge("se_first", &SeCfg::correct(SliceEndKind::First, true, 8), 8);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct split_first must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct `split_last` (head at `len-1`, niche at `f0`) is NOT
    /// refuted.
    #[test]
    fn correct_split_last_is_not_refuted() {
        let outcome = se_discharge("se_last", &SeCfg::correct(SliceEndKind::Last, true, 8), 8);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct split_last must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: the OTHER layout position — the niche in the tail's data
    /// pointer (`f1`), the emitted `Select` there too — is NOT refuted.
    #[test]
    fn correct_split_first_niche_at_f1_is_not_refuted() {
        let outcome =
            se_discharge("se_first_f1", &SeCfg::correct(SliceEndKind::First, false, 8), 8);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct f1-niche split_first must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE control (`size == 1`, e.g. `&[u8]`): `emit_element_addr`'s
    /// identity Mul-skip — the tail data is `data + (1)*1` with NO `Mul` emitted.
    #[test]
    fn correct_split_last_size1_is_not_refuted() {
        let outcome = se_discharge("se_last_s1", &SeCfg::correct(SliceEndKind::Last, true, 1), 1);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 split_last must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY: the emptiness test is INVERTED (`Eq(len,0)`), so the
    /// bridge would yield `Some` on an EMPTY slice -> REFUTED.
    #[test]
    fn inverted_cond_split_first_is_refuted() {
        let cfg = SeCfg {
            cond_op: ICmpOp::Eq,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        let outcome = se_discharge("se_inverted", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an inverted emptiness test must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the `None` niche is NON-NULL (`0xff`), so an empty slice
    /// would decode to `Some(0xff, ..)` -> REFUTED.
    #[test]
    fn nonnull_none_split_first_is_refuted() {
        let cfg = SeCfg {
            none_val: 0xff,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        let outcome = se_discharge("se_nonnull_none", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a non-null None niche must be REFUTED, got {outcome:?}"
        );
    }

    /// THE KEYSTONE: the `Select` is DROPPED — the raw head pointer is stored
    /// UNCONDITIONALLY into the LAYOUT-designated niche cell, so an empty slice
    /// decodes to `Some`. The spec formula for that cell is the ITE (from the
    /// capture-passed `niche_at_f0`, never the emission) while the folded value
    /// is the raw pointer — they differ on `len == 0` -> REFUTED.
    #[test]
    fn dropped_select_unconditional_some_is_refuted() {
        let cfg = SeCfg {
            dropped_select: true,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        let outcome = se_discharge("se_dropped_select", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a dropped niche Select (unconditional Some) must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: `split_last` forgets the `-1` (heads at `data +
    /// len*size`) — a one-past-the-end read -> REFUTED.
    #[test]
    fn wrong_last_index_split_last_is_refuted() {
        let cfg = SeCfg {
            last_minus_one: false,
            ..SeCfg::correct(SliceEndKind::Last, true, 8)
        };
        let outcome = se_discharge("se_wrong_idx", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a last index off by one (no -1) must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the head address scales the index by the WRONG element
    /// size (bridge multiplies by 2, the element is 4 bytes) -> REFUTED.
    #[test]
    fn wrong_scale_split_last_is_refuted() {
        let outcome =
            se_discharge("se_wrong_scale", &SeCfg::correct(SliceEndKind::Last, true, 2), 4);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a wrong element scale must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the pointers are computed off a DIFFERENT base than the
    /// slice data (`SE_WRONGBASE`) -> REFUTED.
    #[test]
    fn wrong_base_split_last_is_refuted() {
        let cfg = SeCfg {
            base: SE_WRONGBASE,
            ..SeCfg::correct(SliceEndKind::Last, true, 8)
        };
        let outcome = se_discharge("se_wrong_base", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "pointers off the wrong base must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: the tail length is the SWAPPED `Sub(one, len)` (`1 - len`
    /// instead of `len - 1`) -> REFUTED.
    #[test]
    fn wrong_sub_direction_tail_len_is_refuted() {
        let cfg = SeCfg {
            tail_len_sub_len_one: false,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        let outcome = se_discharge("se_sub_swap", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a swapped tail-len subtraction must be REFUTED, got {outcome:?}"
        );
    }

    /// KEYSTONE COMPANION: SELECT-ON-WRONG-FIELD — the emitted `Select` flows
    /// into `f1` while the LAYOUT (the obligations' `niche_at_f0 = true`)
    /// designated `f0`. The niche cell gets the raw pointer (unconditional
    /// `Some` on empty) and `f1` gets an ITE the spec says is raw — both cells
    /// differ -> REFUTED. Proves the niche selection comes from the layout,
    /// never from where the emission put the `Select`.
    #[test]
    fn select_on_wrong_field_is_refuted() {
        let cfg = SeCfg {
            select_at_f0: Some(false),
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        let outcome = se_discharge("se_select_wrong_field", &cfg, 8);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a Select emitted into the non-niche field must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK: the unconditional tail-length store is DROPPED — only two
    /// stores fold -> obligations `None` (skip, sound).
    #[test]
    fn missing_tail_len_store_is_out_of_shape() {
        let cfg = SeCfg {
            emit_tail_len: false,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        assert!(
            se_obligations("se_no_tail_len", &cfg, 8).is_none(),
            "a dropped tail-len store must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK: a spurious 4th store -> obligations `None` (skip, sound).
    #[test]
    fn extra_store_is_out_of_shape() {
        let cfg = SeCfg {
            extra_store: true,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        assert!(
            se_obligations("se_extra_store", &cfg, 8).is_none(),
            "an extra 4th store must fail the exact-store-set shape check"
        );
    }

    /// WIDTH GATE: a TRUNCATING 4-byte (`I32`) niche store folds to the
    /// full-width formula but writes only half the cell — the width-checked
    /// shape check must reject it -> obligations `None` (skip, sound).
    #[test]
    fn narrow_niche_store_is_out_of_shape() {
        let cfg = SeCfg {
            niche_store_ty: TrustIrTy::I32,
            ..SeCfg::correct(SliceEndKind::First, true, 8)
        };
        assert!(
            se_obligations("se_narrow_niche", &cfg, 8).is_none(),
            "a 4-byte niche store must fail the width-checked shape check"
        );
    }

    // =======================================================================
    // Lane 9: slice `Iter::next` STATE TRANSITION (the `for x in slice`
    // workhorse — lane-7 `Load -> pre-state symbol` + lane-5 niche `Option<&T>`
    // composed). The emitter hand-builds the EXACT shape `lower_slice_iter_next`
    // emits (the offset-0 `ptr` load shortcut, the stride-1 `iter_field_addr`
    // chain for `end` — NO `Mul` — the `emit_ptr_to_int` `Copy`+`PtrToInt`
    // pairs, the `ICmp Ne`, the `emit_element_addr` advance with the
    // `size == 1` identity Mul-skip, the two `Select`s, and the two typed `Ptr`
    // `Store`s incl. `store_option_some_value`'s Reference arm), so the fold's
    // reconstruction is exercised against the spec end to end — at BOTH element
    // sizes 8 (`&[i64]`, the Mul path) and 1 (`&[u8]`, the Mul-free path).
    // =======================================================================
    const SI_SELF: ValueId = ValueId::new(90);
    const SI_DEST: ValueId = ValueId::new(91);
    /// `slice::Iter`'s cursor layout in the bridge's own model: `ptr` at slot
    /// offset 0, `end` at 8 (`SLICE_ITER_END_OFFSET`).
    const SI_END_OFF: u64 = 8;
    /// `Option<&T>`'s single niche field is the whole 8-byte Option at offset 0.
    const SI_TAG_OFF: u64 = 0;

    #[derive(Clone)]
    struct SiCfg {
        /// The SPEC-side element stride the obligations assert (bytes).
        elem_size: u64,
        /// The EMITTED exhaustion comparison (`Ne` = correct `ptr != end`).
        cmp_op: ICmpOp,
        /// The EMITTED advance stride (`== elem_size` correct; `2*elem_size` =
        /// the wrong-stride bug).
        stride: u64,
        /// `Select(cond, advanced, ptr)` arm order (`false` = advance-when-done).
        advance_in_range: bool,
        /// Build `new_ptr` from the `end` load instead of `ptr` (the
        /// swapped-load-offsets bug: `Ne` is symmetric, so the swap manifests as
        /// the advance running over `ld_o8` written back to `(self, 0)`).
        advance_base_is_end: bool,
        /// The niche `Select` yields the PRE-advance `ptr` (`false` = the
        /// POST-INCREMENT YIELD: `then_val = advanced`, an off-by-one-ELEMENT
        /// read).
        niche_is_pre_ptr: bool,
        /// The `None` niche integer (`0` = correct null).
        none_niche: i128,
        /// Byte offset of the state write-back within the SELF slot (`0` =
        /// correct; `8` clobbers `end` instead).
        writeback_off: u64,
        /// Emit the state write-back store at all (`false` = dropped write-back).
        emit_writeback: bool,
        /// Emit a spurious 3rd store (the shape check must reject).
        extra_store: bool,
        /// The state write-back `Store` type (`Ptr` = the correct 8 bytes; `I32`
        /// = the TRUNCATING write-back of lane-7 adversarial-review defect 2).
        writeback_ty: TrustIrTy,
        /// Defect-1 shape: the niche RELOADS `(self, 0)` AFTER the write-back
        /// store (the post-increment-yield-via-reload emission) instead of using
        /// the pre-state `ptr`. The fold must bail (load-after-store).
        niche_reloads_state: bool,
        /// The pre-state load type (`Ptr` = the correct 8-byte pointer cell;
        /// `I32` = the 4-byte load the width gate must bail on).
        load_ty: TrustIrTy,
    }

    impl SiCfg {
        fn correct(elem_size: u64) -> Self {
            Self {
                elem_size,
                cmp_op: ICmpOp::Ne,
                stride: elem_size,
                advance_in_range: true,
                advance_base_is_end: false,
                niche_is_pre_ptr: true,
                none_niche: 0,
                writeback_off: 0,
                emit_writeback: true,
                extra_store: false,
                writeback_ty: TrustIrTy::Ptr,
                niche_reloads_state: false,
                load_ty: TrustIrTy::Ptr,
            }
        }
    }

    /// `emit_ptr_to_int(ptr)`: `Copy(Ptr)` (the `coerce_to_plain_ptr`
    /// normalization) + `Cast PtrToInt`.
    fn si_ptr_to_int(nodes: &mut Vec<InstrNode>, next: &mut u32, ptr: ValueId) -> ValueId {
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        let pp = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::Ptr,
                operand: ptr,
            },
            pp,
        ));
        let pi = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: pp,
            },
            pi,
        ));
        pi
    }

    fn si_emit(cfg: &SiCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 100u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. ptr = Load(load_ty, SI_SELF)  (`iter_field_addr` offset-0 shortcut:
        //    the ptr address IS the self slot pointer).
        let ptr = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: cfg.load_ty.clone(),
                ptr: SI_SELF,
                volatile: false,
                align: None,
            },
            ptr,
        ));
        // 2. end_addr = iter_field_addr(SI_SELF, 8) (the stride-1 Mul-free
        //    chain); end = Load.
        let end_addr = rn_field_addr(&mut nodes, &mut next, SI_SELF, SI_END_OFF as i128);
        let end = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: cfg.load_ty.clone(),
                ptr: end_addr,
                volatile: false,
                align: None,
            },
            end,
        ));
        // 3. ptr_int / end_int = emit_ptr_to_int (Copy + PtrToInt each);
        //    cond = ICmp(op, ptr_int, end_int).
        let ptr_int = si_ptr_to_int(&mut nodes, &mut next, ptr);
        let end_int = si_ptr_to_int(&mut nodes, &mut next, end);
        let cond = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: cfg.cmp_op,
                ty: TrustIrTy::I64,
                lhs: ptr_int,
                rhs: end_int,
            })
            .with_result(cond),
        );
        // 4. index_one = Const 1; advanced = emit_element_addr(base, one, stride)
        //    (the `size == 1` identity Mul-skip at stride 1) — base is `ptr`, or
        //    `end` for the swapped-loads bug.
        let one = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(1),
            },
            one,
        ));
        let advance_base = if cfg.advance_base_is_end { end } else { ptr };
        let advanced =
            se_element_addr(&mut nodes, &mut next, advance_base, one, cfg.stride as i128);
        // 5. new_ptr = Select(cond, advanced, base)  (or arms swapped).
        let (tv, ev) = if cfg.advance_in_range {
            (advanced, advance_base)
        } else {
            (advance_base, advanced)
        };
        let new_ptr = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::Ptr,
                cond,
                then_val: tv,
                else_val: ev,
            })
            .with_result(new_ptr),
        );
        // 6. Store(writeback_ty, self + writeback_off, new_ptr) — the STATE
        //    WRITE-BACK (offset 0 reuses the slot pointer; offset 8 reuses the
        //    end address; a non-Ptr `writeback_ty` models the TRUNCATING store).
        if cfg.emit_writeback {
            let wb_ptr = if cfg.writeback_off == 0 {
                SI_SELF
            } else {
                assert_eq!(cfg.writeback_off, 8, "test shape only models 0/8");
                end_addr
            };
            nodes.push(InstrNode::new(Inst::Store {
                ty: cfg.writeback_ty.clone(),
                ptr: wb_ptr,
                value: new_ptr,
                volatile: false,
                align: None,
            }));
        }
        // 7. `store_option_some_value` Reference arm: the `None` niche
        //    `Const`+`IntToPtr`, the niche `Select(cond, ptr, none)`, and the
        //    niche store at (dest, 0) (`iter_field_addr` offset-0 shortcut).
        let none_int = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(cfg.none_niche),
            },
            none_int,
        ));
        let none_ptr = fresh(&mut next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: none_int,
            },
            none_ptr,
        ));
        // Defect-1 shape: RELOAD the just-written `(self, 0)` cell and yield THAT
        // (the machine yields `ptr + size` — the post-increment bug via reload;
        // the fold must bail on load-after-store, never bind the reload to the
        // pre-state symbol).
        let yielded = if cfg.niche_reloads_state {
            let reloaded = fresh(&mut next);
            nodes.push(node(
                Inst::Load {
                    ty: cfg.load_ty.clone(),
                    ptr: SI_SELF,
                    volatile: false,
                    align: None,
                },
                reloaded,
            ));
            reloaded
        } else if cfg.niche_is_pre_ptr {
            ptr
        } else {
            advanced
        };
        let chosen = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::Ptr,
                cond,
                then_val: yielded,
                else_val: none_ptr,
            })
            .with_result(chosen),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::Ptr,
            ptr: SI_DEST,
            value: chosen,
            volatile: false,
            align: None,
        }));
        // A spurious 3rd store (shape-check negative).
        if cfg.extra_store {
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::Ptr,
                ptr: end_addr,
                value: chosen,
                volatile: false,
                align: None,
            }));
        }
        nodes
    }

    fn si_obligations(name: &str, cfg: &SiCfg) -> Option<Vec<ProofObligation>> {
        let folded = fold_emitted_slice_iter_next(&si_emit(cfg)).expect("slice Iter::next in slice");
        slice_iter_next_obligations(
            name,
            &folded,
            SI_SELF,
            SI_DEST,
            cfg.elem_size,
            SI_END_OFF,
            SI_TAG_OFF,
        )
    }

    fn si_discharge(name: &str, cfg: &SiCfg) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations = si_obligations(name, cfg).expect("slice Iter::next obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the two stored values as EXACTLY the spec formulas
    /// (over the same pre-state load symbols) for a correct size-8 emission.
    #[test]
    fn fold_reconstructs_slice_iter_next() {
        let cfg = SiCfg::correct(8);
        let folded = fold_emitted_slice_iter_next(&si_emit(&cfg)).expect("in slice");
        let spec = slice_iter_next_spec(
            &ld_value_name(SI_SELF, 0),
            &ld_value_name(SI_SELF, SI_END_OFF),
            8,
        );
        assert_eq!(folded.store_value(SI_SELF, 0).unwrap(), spec.new_ptr);
        assert_eq!(folded.store_value(SI_DEST, SI_TAG_OFF).unwrap(), spec.niche);
    }

    /// POSITIVE: a correct size-8 slice `Iter::next` (`&[i64]`, the `Mul`
    /// advance path) is NOT refuted.
    #[test]
    fn correct_size8_slice_iter_next_is_not_refuted() {
        let outcome = si_discharge("si_size8", &SiCfg::correct(8));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-8 slice Iter::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct size-1 slice `Iter::next` (`&[u8]`,
    /// `emit_element_addr`'s identity Mul-skip — NO `Mul` emitted) is NOT
    /// refuted.
    #[test]
    fn correct_size1_slice_iter_next_is_not_refuted() {
        let outcome = si_discharge("si_size1", &SiCfg::correct(1));
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct size-1 slice Iter::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY (a): INVERTED EXHAUSTION — the bridge emits `Eq` for the
    /// `Ne` exhaustion test, so an exhausted iterator yields `Some` (and a
    /// non-exhausted one `None`) -> REFUTED.
    #[test]
    fn inverted_exhaustion_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            cmp_op: ICmpOp::Eq,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_inverted", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an Eq-for-Ne inverted exhaustion test must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (b): ADVANCE-WHEN-DONE — the `new_ptr` `Select` arms are
    /// swapped (`cond ? ptr : advanced`), so a FINISHED iterator keeps advancing
    /// past its end (and an in-range one never advances: an infinite loop) ->
    /// REFUTED.
    #[test]
    fn advance_when_done_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            advance_in_range: false,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_advance_done", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped new_ptr Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (c): WRONG STRIDE — the advance adds `2*elem_size`, so
    /// the iterator skips every other element -> REFUTED (discharged with the
    /// spec's `elem_size = 8`).
    #[test]
    fn wrong_stride_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            stride: 16,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_stride2", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a 2*size stride must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (d): POST-INCREMENT YIELD — the niche `Select` yields the
    /// ADVANCED pointer (`Some(&*(ptr + size))`) instead of the PRE-advance
    /// `ptr` — an off-by-one-ELEMENT read -> REFUTED.
    #[test]
    fn post_increment_yield_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            niche_is_pre_ptr: false,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a post-increment yield must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (e): NON-NULL `None` (`0xff`), so an exhausted iterator
    /// would decode to `Some(0xff)` -> REFUTED.
    #[test]
    fn nonnull_none_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            none_niche: 0xff,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_nonnull_none", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a non-null None niche must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (f): SWAPPED LOADS — `Ne` is symmetric, so a swapped
    /// `ptr`/`end` load pair manifests as `new_ptr` built from the `end` load
    /// (`Add` over `ld_o8`) written back to `(self, 0)` — it refutes against
    /// the spec's `ptr + size` over `ld_o0` -> REFUTED.
    #[test]
    fn swapped_loads_slice_iter_next_is_refuted() {
        let cfg = SiCfg {
            advance_base_is_end: true,
            ..SiCfg::correct(8)
        };
        let outcome = si_discharge("si_swap_loads", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a new_ptr built from the end load must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK (g): the state write-back targets the END offset `(self, 8)`
    /// instead of `(self, 0)` — an `end`-clobbering store. The store set is not
    /// the exact expected two cells -> obligations `None` (skip, sound).
    #[test]
    fn writeback_to_end_offset_slice_iter_next_is_out_of_shape() {
        let cfg = SiCfg {
            writeback_off: 8,
            ..SiCfg::correct(8)
        };
        assert!(
            si_obligations("si_wb_end", &cfg).is_none(),
            "a write-back to the end offset must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK (h): the state write-back is DROPPED entirely (no self
    /// store). Only one store folds -> obligations `None` (skip, sound — never
    /// a spurious Refined over a missing state transition).
    #[test]
    fn dropped_writeback_slice_iter_next_is_out_of_shape() {
        let cfg = SiCfg {
            emit_writeback: false,
            ..SiCfg::correct(8)
        };
        assert!(
            si_obligations("si_no_wb", &cfg).is_none(),
            "a dropped state write-back must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK (i): a spurious 3rd store -> obligations `None` (skip,
    /// sound).
    #[test]
    fn extra_store_slice_iter_next_is_out_of_shape() {
        let cfg = SiCfg {
            extra_store: true,
            ..SiCfg::correct(8)
        };
        assert!(
            si_obligations("si_extra_store", &cfg).is_none(),
            "an extra 3rd store must fail the exact-store-set shape check"
        );
    }

    /// WIDTH GATE (j): a TRUNCATING 4-byte (`I32`) state write-back folds to
    /// the full 64-bit formula but writes only half the cell (wraps the cursor
    /// at 2^32 -> a wild pointer). The obligations' width-checked shape check
    /// must reject it -> obligations `None` (skip, sound).
    #[test]
    fn narrow_writeback_slice_iter_next_is_out_of_shape() {
        let cfg = SiCfg {
            writeback_ty: TrustIrTy::I32,
            ..SiCfg::correct(8)
        };
        assert!(
            si_obligations("si_narrow_wb", &cfg).is_none(),
            "a 4-byte state write-back must fail the width-checked shape check"
        );
    }

    /// DEFECT-1 REGRESSION (the lane-7 CONFIRMED false-Refined class): the
    /// niche RELOADS the just-written `(self, 0)` cell after the write-back —
    /// the machine yields `ptr + size` (the post-increment bug via reload). The
    /// fold must BAIL on the load-after-store, never bind the reload to the
    /// pre-state symbol.
    #[test]
    fn reload_after_writeback_niche_is_out_of_slice() {
        let cfg = SiCfg {
            niche_reloads_state: true,
            ..SiCfg::correct(8)
        };
        assert!(
            fold_emitted_slice_iter_next(&si_emit(&cfg)).is_none(),
            "a niche reloading the written-back state cell must be out of slice \
             (load-after-store binds no pre-state symbol)"
        );
    }

    /// WIDTH GATE (l): a 4-byte (`I32`) pre-state load takes the fold OUT OF
    /// SLICE — this lane is 8-byte pointer cells only -> fold `None` (skip,
    /// sound).
    #[test]
    fn narrow_load_slice_iter_next_is_out_of_slice() {
        let cfg = SiCfg {
            load_ty: TrustIrTy::I32,
            ..SiCfg::correct(8)
        };
        assert!(
            fold_emitted_slice_iter_next(&si_emit(&cfg)).is_none(),
            "a 4-byte pre-state load must be out of the 8-byte fold slice"
        );
    }

    /// WIDTH-CLASS REGRESSION (lane-9 adversarial finding, solver-CONFIRMED
    /// false-Refined before the gates): a TRUNCATING exhaustion compare —
    /// `PtrToInt` at `I8` + `ICmp` at `I8` — wraps mod 256 at machine level
    /// (the iterator yields `None` mid-slice whenever `end - ptr ≡ 0 (mod
    /// 256)`) while folding at 64 bits STRUCTURALLY EQUAL to the spec. The
    /// Cast/ICmp width gates must take the emission OUT OF SLICE.
    #[test]
    fn narrow_ptrtoint_icmp_slice_iter_next_is_out_of_slice() {
        let mut nodes = si_emit(&SiCfg::correct(8));
        let mut narrowed = 0usize;
        for n in nodes.iter_mut() {
            match &mut n.inst {
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    dst_ty,
                    ..
                } => {
                    *dst_ty = TrustIrTy::I8;
                    narrowed += 1;
                }
                Inst::ICmp { ty, .. } => {
                    *ty = TrustIrTy::I8;
                    narrowed += 1;
                }
                _ => {}
            }
        }
        assert!(narrowed >= 3, "expected to narrow the ptr/end casts + the compare");
        assert!(
            fold_emitted_slice_iter_next(&nodes).is_none(),
            "a truncating I8 exhaustion compare must be out of the fold slice \
             (the solver-confirmed false-Refined of the width class)"
        );
    }

    /// WIDTH-CLASS REGRESSION for the LANDED lane 7 (the same fold arms): a
    /// 4-byte (`I32`) exhaustion `ICmp` in a Range::next emission truncates at
    /// machine level; the ICmp width gate must bail the fold.
    #[test]
    fn narrow_icmp_range_next_is_out_of_slice() {
        let mut nodes = rn_emit(&RnCfg::correct(true));
        for n in nodes.iter_mut() {
            if let Inst::ICmp { ty, .. } = &mut n.inst {
                *ty = TrustIrTy::I32;
            }
        }
        assert!(
            fold_emitted_range_next(&nodes).is_none(),
            "a 4-byte compare must be out of the 8-byte fold slice"
        );
    }

    // =======================================================================
    // Lane 11: `StepBy<Range<i64>>::next` STATE TRANSITION (the WIDTH-FAITHFUL
    // primitives: the NARROW I8 `first_take` load + `ZExt` widening + `Trunc`
    // narrowing folded as explicit 64-bit masking formulas). The emitter
    // hand-builds the EXACT shape `lower_step_by_next`'s SIGNED-Range-i64
    // std-layout path emits (the `Const 0`, the `iter_field_addr` chains — the
    // offset-0 shortcut where an offset is 0 — the I64 `step_minus_one` + I8
    // `first_take` loads, the `ZExt`, the `Ne` + countdown `Select`, the
    // `start`/`end` loads, `y = start + countdown`, the `Sge`/`Slt` guards +
    // Bool `And`, the `new_start`/`new_ft` `Select`s, the `Trunc(I64->I8)`,
    // and the four typed stores incl. `store_option_some_value`'s Direct arm
    // — the i64 identity extend/trunc helpers emit NOTHING, so no I64<->I64
    // casts appear), so the fold's reconstruction is exercised against the
    // spec end to end.
    // =======================================================================
    const SB_SELF: ValueId = ValueId::new(94);
    const SB_DEST: ValueId = ValueId::new(95);
    /// Option<i64>: Some=1 / None=0, tag at slot offset 0, payload at 8.
    const SB_SOME: i128 = 1;
    const SB_NONE: i128 = 0;
    const SB_TAG_OFF: u64 = 0;
    const SB_PAYLOAD_OFF: u64 = 8;

    /// How the emitted `first_take` update behaves.
    #[derive(Clone, Copy, PartialEq)]
    enum SbFtMode {
        /// `new_ft = Select(cond, 0, ft)` — cleared exactly on a yield (correct).
        Cleared,
        /// `new_ft = ft` — never cleared (the iterator re-yields element 0).
        NotCleared,
        /// `new_ft = 0` — cleared unconditionally (an exhausted iterator whose
        /// `first_take` is still set would restart mid-sequence).
        Unconditional,
    }

    #[derive(Clone)]
    struct SbCfg {
        /// Byte offsets of `step_minus_one` / `first_take` / the inner Range.
        sm_off: u64,
        ft_off: u64,
        src_off: u64,
        /// `countdown = Select(ft_nz, 0, sm)` (`false` = arms swapped: the very
        /// first pull yields `start + k` instead of `start`).
        countdown_zero_on_first: bool,
        /// Emit the `Sge` overflow guard + the Bool `And` (`false` = `cond` is
        /// the bare `in_range` — folds fine, REFUTED on the wrap case).
        emit_overflow_guard: bool,
        /// `new_start = Select(cond, y+1, start)` (`false` = advance-when-done).
        advance_in_range: bool,
        /// The `first_take` update mode.
        ft_mode: SbFtMode,
        /// Payload stores `y` (`false` = `y + 1`, the post-increment yield).
        payload_is_y: bool,
        /// Tag `Select(cond, some, none)` arm order (`false` = swapped).
        tag_some_in_range: bool,
        /// The `first_take` store type (`I8` = correct 1-byte; `I64` = the
        /// WIDTH LIE: an 8-byte store clobbering 7 neighbouring bytes).
        ft_store_ty: TrustIrTy,
        /// Emit the `first_take` store at all (`false` = dropped write-back).
        emit_ft_store: bool,
        /// The cursor write-back targets the `end` cell instead of `start`.
        writeback_to_end: bool,
        /// Emit an EXTRA (5th) store to a scratch dest cell.
        emit_extra_store: bool,
        /// The `in_range` `ICmp` type (`I64` correct; `I32` = the lane-10
        /// narrow-compare gate — fold bails).
        in_range_icmp_ty: TrustIrTy,
        /// Defect-1 shape: the payload RELOADS `(self, src_off)` AFTER the
        /// cursor write-back store. The fold must bail (load-after-store).
        payload_reloads_state: bool,
    }

    impl SbCfg {
        /// The correct emission with the canonical std layout
        /// `{ step_minus_one @ 0, first_take @ 8, Range { start @ 16, end @ 24 } }`.
        fn correct() -> Self {
            Self {
                sm_off: 0,
                ft_off: 8,
                src_off: 16,
                countdown_zero_on_first: true,
                emit_overflow_guard: true,
                advance_in_range: true,
                ft_mode: SbFtMode::Cleared,
                payload_is_y: true,
                tag_some_in_range: true,
                ft_store_ty: TrustIrTy::I8,
                emit_ft_store: true,
                writeback_to_end: false,
                emit_extra_store: false,
                in_range_icmp_ty: TrustIrTy::I64,
                payload_reloads_state: false,
            }
        }
    }

    /// `iter_field_addr(base, off)` with the REAL offset-0 shortcut (the raw
    /// base pointer) — `rn_field_addr`'s chain otherwise.
    fn sb_field_addr(
        nodes: &mut Vec<InstrNode>,
        next: &mut u32,
        base: ValueId,
        off: u64,
    ) -> ValueId {
        if off == 0 {
            base
        } else {
            rn_field_addr(nodes, next, base, off as i128)
        }
    }

    fn sb_emit(cfg: &SbCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 300u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. zero = Const 0 (`emit_i64_const`).
        let zero_c = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0),
            },
            zero_c,
        ));
        // 2. state_addr / ft_addr chains (`iter_field_addr`).
        let state_addr = sb_field_addr(&mut nodes, &mut next, SB_SELF, cfg.sm_off);
        let ft_addr = sb_field_addr(&mut nodes, &mut next, SB_SELF, cfg.ft_off);
        // 3. sm = Load(I64); ft_i8 = Load(I8)  (the NARROW load).
        let sm = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: state_addr,
                volatile: false,
                align: None,
            },
            sm,
        ));
        let ft_i8 = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I8,
                ptr: ft_addr,
                volatile: false,
                align: None,
            },
            ft_i8,
        ));
        // 4. ft = ZExt(I8 -> I64)  (`emit_extend_to_i64`, unsigned).
        let ft = fresh(&mut next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: TrustIrTy::I8,
                dst_ty: TrustIrTy::I64,
                operand: ft_i8,
            },
            ft,
        ));
        // 5. ft_nz = ICmp Ne(ft, 0); countdown = Select(ft_nz, 0, sm).
        let ft_nz = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: TrustIrTy::I64,
                lhs: ft,
                rhs: zero_c,
            })
            .with_result(ft_nz),
        );
        let (cd_t, cd_e) = if cfg.countdown_zero_on_first {
            (zero_c, sm)
        } else {
            (sm, zero_c)
        };
        let countdown = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I64,
                cond: ft_nz,
                then_val: cd_t,
                else_val: cd_e,
            })
            .with_result(countdown),
        );
        // 6. start / end loads (I64 elements — the widening `emit_extend_to_i64`
        //    calls are IDENTITY for i64: NOTHING is emitted).
        let start_addr = sb_field_addr(&mut nodes, &mut next, SB_SELF, cfg.src_off);
        let start = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: start_addr,
                volatile: false,
                align: None,
            },
            start,
        ));
        let end_addr = sb_field_addr(&mut nodes, &mut next, SB_SELF, cfg.src_off + 8);
        let end = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: end_addr,
                volatile: false,
                align: None,
            },
            end,
        ));
        // 7. y = Add(start, countdown).
        let y = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: start,
                rhs: countdown,
            })
            .with_result(y),
        );
        // 8. no_overflow = ICmp Sge(y, start); in_range = ICmp Slt(y, end);
        //    cond = And(Bool, no, in)  (`emit_bool_and`). The guard-dropping
        //    variant wires `cond = in_range` directly.
        let in_range = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: cfg.in_range_icmp_ty.clone(),
                lhs: y,
                rhs: end,
            })
            .with_result(in_range),
        );
        let cond = if cfg.emit_overflow_guard {
            let no_overflow = fresh(&mut next);
            nodes.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: TrustIrTy::I64,
                    lhs: y,
                    rhs: start,
                })
                .with_result(no_overflow),
            );
            let cond = fresh(&mut next);
            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: TrustIrBinOp::And,
                    ty: TrustIrTy::Bool,
                    lhs: no_overflow,
                    rhs: in_range,
                })
                .with_result(cond),
            );
            cond
        } else {
            in_range
        };
        // 9. yval = trunc(y) IDENTITY (nothing emitted); y_plus1 = Add(y, 1);
        //    new_start_yield = trunc IDENTITY; new_start = Select(cond,
        //    y_plus1, start); Store(I64 @ src_off) — STORE 1 (cursor).
        let one = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(1),
            },
            one,
        ));
        let y_plus1 = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: y,
                rhs: one,
            })
            .with_result(y_plus1),
        );
        let (ns_t, ns_e) = if cfg.advance_in_range {
            (y_plus1, start)
        } else {
            (start, y_plus1)
        };
        let new_start = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I64,
                cond,
                then_val: ns_t,
                else_val: ns_e,
            })
            .with_result(new_start),
        );
        let wb_addr = if cfg.writeback_to_end { end_addr } else { start_addr };
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::I64,
            ptr: wb_addr,
            value: new_start,
            volatile: false,
            align: None,
        }));
        // 10. new_ft = Select(cond, 0, ft); new_ft8 = Trunc(I64 -> I8);
        //     Store(I8 @ ft_off) — STORE 2 (first_take, WIDTH 1). The width-lie
        //     variant stores the un-truncated I64; the mode variants change the
        //     stored value.
        if cfg.emit_ft_store {
            let new_ft = match cfg.ft_mode {
                SbFtMode::Cleared => {
                    let new_ft = fresh(&mut next);
                    nodes.push(
                        InstrNode::new(Inst::Select {
                            ty: TrustIrTy::I64,
                            cond,
                            then_val: zero_c,
                            else_val: ft,
                        })
                        .with_result(new_ft),
                    );
                    new_ft
                }
                SbFtMode::NotCleared => ft,
                SbFtMode::Unconditional => zero_c,
            };
            if cfg.ft_store_ty == TrustIrTy::I8 {
                let new_ft8 = fresh(&mut next);
                nodes.push(node(
                    Inst::Cast {
                        op: CastOp::Trunc,
                        src_ty: TrustIrTy::I64,
                        dst_ty: TrustIrTy::I8,
                        operand: new_ft,
                    },
                    new_ft8,
                ));
                nodes.push(InstrNode::new(Inst::Store {
                    ty: TrustIrTy::I8,
                    ptr: ft_addr,
                    value: new_ft8,
                    volatile: false,
                    align: None,
                }));
            } else {
                nodes.push(InstrNode::new(Inst::Store {
                    ty: cfg.ft_store_ty.clone(),
                    ptr: ft_addr,
                    value: new_ft,
                    volatile: false,
                    align: None,
                }));
            }
        }
        // 11. `store_option_some_value` Direct arm: I8 tag Consts + Select +
        //     Store @ (dest, 0) (offset-0 shortcut) — STORE 3; payload
        //     Store(I64 @ (dest, 8)) — STORE 4.
        let some_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I8,
                value: Constant::Int(SB_SOME),
            },
            some_tag,
        ));
        let none_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I8,
                value: Constant::Int(SB_NONE),
            },
            none_tag,
        ));
        let (tt, te) = if cfg.tag_some_in_range {
            (some_tag, none_tag)
        } else {
            (none_tag, some_tag)
        };
        let chosen_tag = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I8,
                cond,
                then_val: tt,
                else_val: te,
            })
            .with_result(chosen_tag),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::I8,
            ptr: SB_DEST,
            value: chosen_tag,
            volatile: false,
            align: None,
        }));
        let payload_addr =
            rn_field_addr(&mut nodes, &mut next, SB_DEST, SB_PAYLOAD_OFF as i128);
        // Defect-1 shape: RELOAD the just-written cursor cell and yield THAT.
        let payload = if cfg.payload_reloads_state {
            let reloaded = fresh(&mut next);
            nodes.push(node(
                Inst::Load {
                    ty: TrustIrTy::I64,
                    ptr: start_addr,
                    volatile: false,
                    align: None,
                },
                reloaded,
            ));
            reloaded
        } else if cfg.payload_is_y {
            y
        } else {
            y_plus1
        };
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::I64,
            ptr: payload_addr,
            value: payload,
            volatile: false,
            align: None,
        }));
        // An EXTRA (5th) store to a scratch dest cell.
        if cfg.emit_extra_store {
            let scratch_addr = rn_field_addr(&mut nodes, &mut next, SB_DEST, 16);
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::I64,
                ptr: scratch_addr,
                value: y,
                volatile: false,
                align: None,
            }));
        }
        nodes
    }

    fn sb_obligations(name: &str, cfg: &SbCfg) -> Option<Vec<ProofObligation>> {
        let folded = fold_emitted_step_by_next(&sb_emit(cfg)).expect("StepBy::next in slice");
        step_by_next_obligations(
            name,
            &folded,
            SB_SELF,
            SB_DEST,
            cfg.sm_off,
            cfg.ft_off,
            cfg.src_off,
            SB_TAG_OFF,
            1,
            SB_PAYLOAD_OFF,
            SB_SOME as u64,
            SB_NONE as u64,
        )
    }

    fn sb_discharge(name: &str, cfg: &SbCfg) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations = sb_obligations(name, cfg).expect("StepBy::next obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the four stored values as EXACTLY the spec
    /// formulas (over the same pre-state load symbols — the NARROW `first_take`
    /// load's masked 64-bit formula included) for a correct emission.
    #[test]
    fn fold_reconstructs_step_by_next() {
        let cfg = SbCfg::correct();
        let folded = fold_emitted_step_by_next(&sb_emit(&cfg)).expect("in slice");
        let spec = step_by_next_spec(
            &ld_value_name(SB_SELF, cfg.sm_off),
            &ld_value_name_w(SB_SELF, cfg.ft_off, 1),
            &ld_value_name(SB_SELF, cfg.src_off),
            &ld_value_name(SB_SELF, cfg.src_off + 8),
            SB_SOME as u64,
            SB_NONE as u64,
            1,
        );
        assert_eq!(
            folded.store_value(SB_SELF, cfg.src_off).unwrap(),
            spec.new_start
        );
        assert_eq!(folded.store_value(SB_SELF, cfg.ft_off).unwrap(), spec.new_ft);
        assert_eq!(folded.store_value(SB_DEST, SB_TAG_OFF).unwrap(), spec.tag);
        assert_eq!(
            folded.store_value(SB_DEST, SB_PAYLOAD_OFF).unwrap(),
            spec.payload
        );
    }

    /// POSITIVE: a correct `StepBy<Range<i64>>::next` is NOT refuted (the
    /// `ft = 0` and `ft = 1` paths are the SAME branchless emission — one
    /// positive covers both pulls).
    #[test]
    fn correct_step_by_next_is_not_refuted() {
        let outcome = sb_discharge("sb_correct", &SbCfg::correct());
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct emission under a DIFFERENT slot layout
    /// (`sm_off/ft_off/src_off = 16/24/0` — the Range first, so the cursor
    /// load/store use the offset-0 shortcut) is NOT refuted.
    #[test]
    fn correct_step_by_next_alt_offsets_is_not_refuted() {
        let cfg = SbCfg {
            sm_off: 16,
            ft_off: 24,
            src_off: 0,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_alt_offsets", &cfg);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct alt-layout StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY (a): COUNTDOWN ARMS SWAPPED — the very first pull yields
    /// `start + (k-1)` instead of `start` (and every later pull yields the
    /// un-stepped `start`) -> REFUTED.
    #[test]
    fn swapped_countdown_arms_step_by_next_is_refuted() {
        let cfg = SbCfg {
            countdown_zero_on_first: false,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_countdown_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped countdown Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (b): DROPPED OVERFLOW GUARD — `cond` is the bare
    /// `in_range` (`And(no_overflow, in_range)` degenerates to `in_range`).
    /// The emission FOLDS fine, but on a wrapped `y` (`start` near `i64::MAX`)
    /// the machine yields a bogus `Some` where std's `forward_checked` says
    /// `None` -> REFUTED by the obligation, not the shape.
    #[test]
    fn missing_overflow_guard_step_by_next_is_refuted() {
        let cfg = SbCfg {
            emit_overflow_guard: false,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_no_guard", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a dropped Sge overflow guard must be REFUTED on the wrap case, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (c): ADVANCE-WHEN-DONE — the `new_start` `Select` arms
    /// are swapped (a finished iterator keeps advancing; an in-range one never
    /// does) -> REFUTED.
    #[test]
    fn advance_when_done_step_by_next_is_refuted() {
        let cfg = SbCfg {
            advance_in_range: false,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_advance_done", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped new_start Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (d): FIRST_TAKE NEVER CLEARED — `new_ft = ft` (the
    /// iterator would re-yield element 0 forever). The 1-byte store folds to
    /// `ft & 0xff` where the spec has `ITE(cond, 0, ft) & 0xff` -> REFUTED on
    /// the low-byte compare.
    #[test]
    fn ft_not_cleared_step_by_next_is_refuted() {
        let cfg = SbCfg {
            ft_mode: SbFtMode::NotCleared,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_ft_not_cleared", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a never-cleared first_take must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (e): FIRST_TAKE CLEARED UNCONDITIONALLY — `new_ft = 0`
    /// even on the `None` edge (an exhausted iterator whose `first_take` is
    /// still set would RESTART mid-sequence on a later pull) -> REFUTED.
    #[test]
    fn ft_cleared_unconditionally_step_by_next_is_refuted() {
        let cfg = SbCfg {
            ft_mode: SbFtMode::Unconditional,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_ft_unconditional", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an unconditionally-cleared first_take must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (f): POST-INCREMENT PAYLOAD — the payload stores `y + 1`
    /// instead of `y` (every yielded value off by one) -> REFUTED.
    #[test]
    fn post_increment_payload_step_by_next_is_refuted() {
        let cfg = SbCfg {
            payload_is_y: false,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a post-increment payload must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY (g): TAG ARMS SWAPPED — `None` on an in-range element,
    /// `Some` on exhaustion -> REFUTED.
    #[test]
    fn swapped_tag_arms_step_by_next_is_refuted() {
        let cfg = SbCfg {
            tag_some_in_range: false,
            ..SbCfg::correct()
        };
        let outcome = sb_discharge("sb_tag_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped tag Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK (h): WIDTH LIE — the `first_take` store is emitted at 8
    /// BYTES (clobbering the 7 bytes after the 1-byte cell). The store set is
    /// width-checked against the expected `(self, ft_off, 1)` -> obligations
    /// `None` (skip, sound).
    #[test]
    fn wide_ft_store_step_by_next_is_out_of_shape() {
        let cfg = SbCfg {
            ft_store_ty: TrustIrTy::I64,
            ..SbCfg::correct()
        };
        assert!(
            sb_obligations("sb_wide_ft", &cfg).is_none(),
            "an 8-byte first_take store must fail the width-exact shape check"
        );
    }

    /// SHAPE CHECK (i): the `first_take` store is DROPPED entirely. Only three
    /// stores fold -> obligations `None` (skip, sound — never a spurious
    /// Refined over a missing state transition).
    #[test]
    fn missing_ft_store_step_by_next_is_out_of_shape() {
        let cfg = SbCfg {
            emit_ft_store: false,
            ..SbCfg::correct()
        };
        assert!(
            sb_obligations("sb_no_ft", &cfg).is_none(),
            "a dropped first_take store must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK (j): an EXTRA (5th) store -> obligations `None` (skip,
    /// sound — an unexpected write is never blessed).
    #[test]
    fn extra_store_step_by_next_is_out_of_shape() {
        let cfg = SbCfg {
            emit_extra_store: true,
            ..SbCfg::correct()
        };
        assert!(
            sb_obligations("sb_extra", &cfg).is_none(),
            "an extra store must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK (k): the cursor write-back targets the `end` cell
    /// (`src_off + 8`) instead of `start` — an `end`-clobbering store. The
    /// store set misses the expected `(self, src_off, 8)` cell -> obligations
    /// `None` (skip, sound).
    #[test]
    fn writeback_to_end_cell_step_by_next_is_out_of_shape() {
        let cfg = SbCfg {
            writeback_to_end: true,
            ..SbCfg::correct()
        };
        assert!(
            sb_obligations("sb_wb_end", &cfg).is_none(),
            "a write-back to the end cell must fail the exact-store-set shape check"
        );
    }

    /// WIDTH GATE (l, the lane-10 class): a 4-byte (`I32`) `in_range` `ICmp`
    /// truncates at machine level; the hard 8-byte ICmp gate must bail the
    /// fold (the lane-11 width relaxation applies ONLY to the ZExt/Trunc/
    /// narrow-load masking arms, never to compares).
    #[test]
    fn narrow_icmp_step_by_next_is_out_of_slice() {
        let cfg = SbCfg {
            in_range_icmp_ty: TrustIrTy::I32,
            ..SbCfg::correct()
        };
        assert!(
            fold_emitted_step_by_next(&sb_emit(&cfg)).is_none(),
            "a 4-byte compare must be out of the 8-byte fold slice"
        );
    }

    /// DEFECT-1 REGRESSION (the lane-7 load-after-store class): the payload
    /// RELOADS the just-written cursor cell after the write-back — the machine
    /// yields `y + 1` on the yield edge (the post-increment bug via reload).
    /// The fold must BAIL on the load-after-store, never bind the reload to
    /// the pre-state symbol.
    #[test]
    fn reload_after_writeback_payload_step_by_next_is_out_of_slice() {
        let cfg = SbCfg {
            payload_reloads_state: true,
            ..SbCfg::correct()
        };
        assert!(
            fold_emitted_step_by_next(&sb_emit(&cfg)).is_none(),
            "a payload reloading the written-back cursor cell must be out of slice \
             (load-after-store binds no pre-state symbol)"
        );
    }

    // =======================================================================
    // StepBy v2 lane 12a — PACKED-UNSIGNED Range (`(0..n u64/usize).step_by(k)`)
    // fixture: hand-builds the EXACT shape `lower_step_by_next`'s packed path
    // emits (the DEAD `Const 0` + DEAD `first_take` address chain — both
    // emitted unconditionally before the path split — the packed-state I64
    // load, the `And(state, 0xFFFF_FFFF)` countdown, the `LShr(state, 32)`
    // reset, the `Shl`/`Or` rebuilding `(k-1)<<32 | (k-1)`, the U64
    // `start`/`end` loads (the u64 identity extends emit NOTHING), the
    // `y = Add(start, countdown)`, the UNSIGNED `Uge`/`Ult` guards + Bool
    // `And`, the `new_start`/`new_state`/tag `Select`s, and the four typed
    // stores incl. `store_option_some_value`'s Direct arm), so the fold's new
    // arithmetic `And`/`Or`/`Shl`/`LShr` arms are exercised against the
    // packed spec end to end.
    // =======================================================================
    const SBP_SELF: ValueId = ValueId::new(96);
    const SBP_DEST: ValueId = ValueId::new(97);
    /// Option<u64>: Some=1 / None=0, tag at slot offset 0, payload at 8.
    const SBP_SOME: i128 = 1;
    const SBP_NONE: i128 = 0;
    const SBP_TAG_OFF: u64 = 0;
    const SBP_PAYLOAD_OFF: u64 = 8;

    #[derive(Clone)]
    struct SbpCfg {
        /// Byte offsets of the packed state word / the (DEAD) `first_take`
        /// cell / the inner Range.
        sm_off: u64,
        ft_off: u64,
        src_off: u64,
        /// `countdown = state & 0xFFFF_FFFF` (`false` = countdown taken from
        /// the HIGH half: the `LShr` result feeds `y` and the `And` result
        /// feeds the state rebuild — the first pull yields `start + (k-1)`).
        countdown_low_half: bool,
        /// Emit the `Uge` overflow guard + the Bool `And` (`false` = `cond`
        /// is the bare `in_range`).
        emit_overflow_guard: bool,
        /// `new_start = Select(cond, y+1, start)` (`false` = advance-when-done).
        advance_in_range: bool,
        /// `new_state = Select(cond, new_state_yield, state)` (`false` =
        /// reset arms swapped: the state LOSES `k` on a yield).
        state_yield_in_range: bool,
        /// The state store bypasses the `Select` and writes `new_state_yield`
        /// UNCONDITIONALLY (an exhausted iterator's countdown resets to `k-1`
        /// — the restart bug).
        state_unconditional: bool,
        /// Payload stores `y` (`false` = `y + 1`, the post-increment yield).
        payload_is_y: bool,
        /// Tag `Select(cond, some, none)` arm order (`false` = swapped).
        tag_some_in_range: bool,
        /// Emit the packed-state store at all (`false` = dropped write-back).
        emit_state_store: bool,
        /// The packed-state store type (`I64` correct; `I32` = the WIDTH LIE:
        /// a 4-byte store dropping the high `k-1` half).
        state_store_ty: TrustIrTy,
        /// Emit an EXTRA (5th) store to a scratch dest cell.
        emit_extra_store: bool,
    }

    impl SbpCfg {
        /// The correct emission with the canonical layout
        /// `{ Range { start @ 0, end @ 8 }, state @ 16, first_take @ 24 }`.
        fn correct() -> Self {
            Self {
                sm_off: 16,
                ft_off: 24,
                src_off: 0,
                countdown_low_half: true,
                emit_overflow_guard: true,
                advance_in_range: true,
                state_yield_in_range: true,
                state_unconditional: false,
                payload_is_y: true,
                tag_some_in_range: true,
                emit_state_store: true,
                state_store_ty: TrustIrTy::I64,
                emit_extra_store: false,
            }
        }
    }

    fn sbp_emit(cfg: &SbpCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 400u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. zero = Const 0 (`emit_i64_const` — DEAD on the packed path but
        //    emitted unconditionally before the path split).
        let zero_c = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0),
            },
            zero_c,
        ));
        // 2. state_addr / ft_addr chains (`iter_field_addr` — the ft chain is
        //    DEAD on the packed path but emitted unconditionally).
        let state_addr = sb_field_addr(&mut nodes, &mut next, SBP_SELF, cfg.sm_off);
        let _ft_addr = sb_field_addr(&mut nodes, &mut next, SBP_SELF, cfg.ft_off);
        // 3. state = Load(I64 @ sm_off) — the ONE packed word.
        let state = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: state_addr,
                volatile: false,
                align: None,
            },
            state,
        ));
        // 4. lo_mask = Const 0xFFFF_FFFF; and_r = And(I64, state, lo_mask);
        //    shift32 = Const 32; shr_r = LShr(I64, state, shift32).
        let lo_mask = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0xFFFF_FFFF),
            },
            lo_mask,
        ));
        let and_r = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::And,
                ty: TrustIrTy::I64,
                lhs: state,
                rhs: lo_mask,
            })
            .with_result(and_r),
        );
        let shift32 = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(32),
            },
            shift32,
        ));
        let shr_r = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::LShr,
                ty: TrustIrTy::I64,
                lhs: state,
                rhs: shift32,
            })
            .with_result(shr_r),
        );
        // The correct emission: countdown = the AND (low half), reset = the
        // LShr (high half). The countdown-from-high-half bug swaps the ROLES.
        let (countdown, reset) = if cfg.countdown_low_half {
            (and_r, shr_r)
        } else {
            (shr_r, and_r)
        };
        // 5. reset_hi = Shl(I64, reset, 32); new_state_yield = Or(reset_hi, reset).
        let reset_hi = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Shl,
                ty: TrustIrTy::I64,
                lhs: reset,
                rhs: shift32,
            })
            .with_result(reset_hi),
        );
        let new_state_yield = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Or,
                ty: TrustIrTy::I64,
                lhs: reset_hi,
                rhs: reset,
            })
            .with_result(new_state_yield),
        );
        // 6. start / end loads (U64 elements — the u64 identity extends emit
        //    NOTHING).
        let start_addr = sb_field_addr(&mut nodes, &mut next, SBP_SELF, cfg.src_off);
        let start = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::U64,
                ptr: start_addr,
                volatile: false,
                align: None,
            },
            start,
        ));
        let end_addr = sb_field_addr(&mut nodes, &mut next, SBP_SELF, cfg.src_off + 8);
        let end = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::U64,
                ptr: end_addr,
                volatile: false,
                align: None,
            },
            end,
        ));
        // 7. y = Add(I64, start, countdown).
        let y = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: start,
                rhs: countdown,
            })
            .with_result(y),
        );
        // 8. UNSIGNED guards: in_range = Ult(y, end); no_overflow = Uge(y,
        //    start); cond = And(Bool). The guard-dropping variant wires
        //    `cond = in_range` directly.
        let in_range = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: TrustIrTy::I64,
                lhs: y,
                rhs: end,
            })
            .with_result(in_range),
        );
        let cond = if cfg.emit_overflow_guard {
            let no_overflow = fresh(&mut next);
            nodes.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Uge,
                    ty: TrustIrTy::I64,
                    lhs: y,
                    rhs: start,
                })
                .with_result(no_overflow),
            );
            let cond = fresh(&mut next);
            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: TrustIrBinOp::And,
                    ty: TrustIrTy::Bool,
                    lhs: no_overflow,
                    rhs: in_range,
                })
                .with_result(cond),
            );
            cond
        } else {
            in_range
        };
        // 9. y_plus1 = Add(y, 1); new_start = Select(U64, cond, y_plus1,
        //    start); Store(U64 @ src_off) — STORE 1 (cursor).
        let one = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(1),
            },
            one,
        ));
        let y_plus1 = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: y,
                rhs: one,
            })
            .with_result(y_plus1),
        );
        let (ns_t, ns_e) = if cfg.advance_in_range {
            (y_plus1, start)
        } else {
            (start, y_plus1)
        };
        let new_start = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::U64,
                cond,
                then_val: ns_t,
                else_val: ns_e,
            })
            .with_result(new_start),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::U64,
            ptr: start_addr,
            value: new_start,
            volatile: false,
            align: None,
        }));
        // 10. new_state = Select(I64, cond, new_state_yield, state);
        //     Store(I64 @ sm_off) — STORE 2 (the packed word). The
        //     unconditional variant stores `new_state_yield` with no Select;
        //     the swapped variant flips the arms; the width-lie variant
        //     stores at I32.
        if cfg.emit_state_store {
            let stored_state = if cfg.state_unconditional {
                new_state_yield
            } else {
                let (st_t, st_e) = if cfg.state_yield_in_range {
                    (new_state_yield, state)
                } else {
                    (state, new_state_yield)
                };
                let new_state = fresh(&mut next);
                nodes.push(
                    InstrNode::new(Inst::Select {
                        ty: TrustIrTy::I64,
                        cond,
                        then_val: st_t,
                        else_val: st_e,
                    })
                    .with_result(new_state),
                );
                new_state
            };
            nodes.push(InstrNode::new(Inst::Store {
                ty: cfg.state_store_ty.clone(),
                ptr: state_addr,
                value: stored_state,
                volatile: false,
                align: None,
            }));
        }
        // 11. `store_option_some_value` Direct arm: I8 tag Consts + Select +
        //     Store @ (dest, 0) — STORE 3; payload Store(U64 @ (dest, 8)) —
        //     STORE 4.
        let some_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I8,
                value: Constant::Int(SBP_SOME),
            },
            some_tag,
        ));
        let none_tag = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I8,
                value: Constant::Int(SBP_NONE),
            },
            none_tag,
        ));
        let (tt, te) = if cfg.tag_some_in_range {
            (some_tag, none_tag)
        } else {
            (none_tag, some_tag)
        };
        let chosen_tag = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I8,
                cond,
                then_val: tt,
                else_val: te,
            })
            .with_result(chosen_tag),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::I8,
            ptr: SBP_DEST,
            value: chosen_tag,
            volatile: false,
            align: None,
        }));
        let payload_addr =
            rn_field_addr(&mut nodes, &mut next, SBP_DEST, SBP_PAYLOAD_OFF as i128);
        let payload = if cfg.payload_is_y { y } else { y_plus1 };
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::U64,
            ptr: payload_addr,
            value: payload,
            volatile: false,
            align: None,
        }));
        // An EXTRA (5th) store to a scratch dest cell.
        if cfg.emit_extra_store {
            let scratch_addr = rn_field_addr(&mut nodes, &mut next, SBP_DEST, 16);
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::I64,
                ptr: scratch_addr,
                value: y,
                volatile: false,
                align: None,
            }));
        }
        nodes
    }

    fn sbp_obligations(name: &str, cfg: &SbpCfg) -> Option<Vec<ProofObligation>> {
        let folded =
            fold_emitted_step_by_next(&sbp_emit(cfg)).expect("packed StepBy::next in slice");
        step_by_next_packed_obligations(
            name,
            &folded,
            SBP_SELF,
            SBP_DEST,
            cfg.sm_off,
            cfg.src_off,
            SBP_TAG_OFF,
            1,
            SBP_PAYLOAD_OFF,
            SBP_SOME as u64,
            SBP_NONE as u64,
        )
    }

    fn sbp_discharge(name: &str, cfg: &SbpCfg) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations =
            sbp_obligations(name, cfg).expect("packed StepBy::next obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the four stored values as EXACTLY the packed
    /// spec formulas (over the same pre-state load symbols — the
    /// `And`/`LShr`/`Shl`/`Or` prelude folded bit-exactly) for a correct
    /// emission.
    #[test]
    fn fold_reconstructs_step_by_next_packed() {
        let cfg = SbpCfg::correct();
        let folded = fold_emitted_step_by_next(&sbp_emit(&cfg)).expect("in slice");
        let spec = step_by_next_packed_spec(
            &ld_value_name(SBP_SELF, cfg.sm_off),
            &ld_value_name(SBP_SELF, cfg.src_off),
            &ld_value_name(SBP_SELF, cfg.src_off + 8),
            SBP_SOME as u64,
            SBP_NONE as u64,
            1,
        );
        assert_eq!(
            folded.store_value(SBP_SELF, cfg.src_off).unwrap(),
            spec.new_start
        );
        assert_eq!(
            folded.store_value(SBP_SELF, cfg.sm_off).unwrap(),
            spec.new_state
        );
        assert_eq!(folded.store_value(SBP_DEST, SBP_TAG_OFF).unwrap(), spec.tag);
        assert_eq!(
            folded.store_value(SBP_DEST, SBP_PAYLOAD_OFF).unwrap(),
            spec.payload
        );
    }

    /// POSITIVE: a correct packed-unsigned `StepBy<Range<u64>>::next` is NOT
    /// refuted.
    #[test]
    fn correct_step_by_next_packed_is_not_refuted() {
        let outcome = sbp_discharge("sbp_correct", &SbpCfg::correct());
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct packed StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct packed emission under a DIFFERENT slot layout
    /// (`sm_off/ft_off/src_off = 0/8/16` — the state word first, so its
    /// load/store use the offset-0 shortcut) is NOT refuted.
    #[test]
    fn correct_step_by_next_packed_alt_offsets_is_not_refuted() {
        let cfg = SbpCfg {
            sm_off: 0,
            ft_off: 8,
            src_off: 16,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_alt_offsets", &cfg);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct alt-layout packed StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY: RESET ARMS SWAPPED — `new_state = Select(cond, state,
    /// new_state_yield)`: on a yield the state KEEPS its spent countdown (the
    /// iterator loses `k` and yields consecutive elements) -> REFUTED.
    #[test]
    fn swapped_reset_arms_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            state_yield_in_range: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_reset_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped new_state Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: COUNTDOWN FROM THE HIGH HALF — `y = start +
    /// (state >> 32)` (and the state rebuild uses the low half): the first
    /// pull yields `start + (k-1)` instead of `start` -> REFUTED.
    #[test]
    fn countdown_from_high_half_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            countdown_low_half: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_high_half", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a countdown taken from the high packed half must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: DROPPED OVERFLOW GUARD — `cond` is the bare `Ult`. On
    /// a wrapped `y` (`start` near `u64::MAX`) the machine yields a bogus
    /// `Some` where std's `forward_checked` says `None` -> REFUTED by the
    /// obligation, not the shape.
    #[test]
    fn missing_overflow_guard_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            emit_overflow_guard: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_no_guard", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a dropped Uge overflow guard must be REFUTED on the wrap case, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: ADVANCE-WHEN-DONE — the `new_start` `Select` arms are
    /// swapped -> REFUTED.
    #[test]
    fn advance_when_done_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            advance_in_range: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_advance_done", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped new_start Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: POST-INCREMENT PAYLOAD — the payload stores `y + 1`
    /// -> REFUTED.
    #[test]
    fn post_increment_payload_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            payload_is_y: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a post-increment payload must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: TAG ARMS SWAPPED -> REFUTED.
    #[test]
    fn swapped_tag_arms_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            tag_some_in_range: false,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_tag_swap", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "swapped tag Select arms must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: STATE WRITTEN UNCONDITIONALLY — the packed word is
    /// rebuilt to `(k-1)<<32 | (k-1)` even on the `None` edge (an EXHAUSTED
    /// iterator's spent countdown resets — a later `end` bump would RESTART
    /// the sequence mid-stride) -> REFUTED.
    #[test]
    fn unconditional_state_reset_step_by_next_packed_is_refuted() {
        let cfg = SbpCfg {
            state_unconditional: true,
            ..SbpCfg::correct()
        };
        let outcome = sbp_discharge("sbp_state_uncond", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "an unconditionally-reset packed state must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK: the packed-state store is DROPPED entirely. Only three
    /// stores fold -> obligations `None` (skip, sound — never a spurious
    /// Refined over a missing state transition).
    #[test]
    fn missing_state_store_step_by_next_packed_is_out_of_shape() {
        let cfg = SbpCfg {
            emit_state_store: false,
            ..SbpCfg::correct()
        };
        assert!(
            sbp_obligations("sbp_no_state", &cfg).is_none(),
            "a dropped packed-state store must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK: an EXTRA (5th) store -> obligations `None` (skip, sound).
    #[test]
    fn extra_store_step_by_next_packed_is_out_of_shape() {
        let cfg = SbpCfg {
            emit_extra_store: true,
            ..SbpCfg::correct()
        };
        assert!(
            sbp_obligations("sbp_extra", &cfg).is_none(),
            "an extra store must fail the exact-store-set shape check"
        );
    }

    /// SHAPE CHECK: WIDTH LIE — the packed-state store is emitted at 4 BYTES
    /// (dropping the high `k-1` half). The store set is width-checked against
    /// the expected `(self, sm_off, 8)` -> obligations `None` (skip, sound).
    #[test]
    fn narrow_state_store_step_by_next_packed_is_out_of_shape() {
        let cfg = SbpCfg {
            state_store_ty: TrustIrTy::I32,
            ..SbpCfg::correct()
        };
        assert!(
            sbp_obligations("sbp_narrow_state", &cfg).is_none(),
            "a 4-byte packed-state store must fail the width-exact shape check"
        );
    }

    // =======================================================================
    // StepBy v2 lane 12b — STD-LAYOUT SLICE source (`v.iter().step_by(k)`)
    // fixture: hand-builds the EXACT shape `lower_step_by_next`'s slice path
    // emits (the std prelude IDENTICAL to v1 — `Const 0`, the address chains,
    // the `sm` I64 + `first_take` I8 NARROW loads, the `ZExt`, the `Ne` +
    // countdown `Select` — then the `{ptr, end}` Ptr loads, the
    // `emit_element_addr` stride arithmetic (the `Copy`/`PtrToInt`/`Mul`/
    // `Add`/`IntToPtr` chain, the `Mul` present iff stride != 1), the
    // `PtrToInt`x3, the UNSIGNED `Uge`/`Ult` guards + Bool `And`, the
    // `new_ptr`/`new_ft` `Select`s + `Trunc`, and
    // `store_option_some_value`'s Reference/NICHE arm — the `Const 0` +
    // `IntToPtr` null, the niche `Select`, and the three typed stores).
    // =======================================================================
    const SBS_SELF: ValueId = ValueId::new(98);
    const SBS_DEST: ValueId = ValueId::new(99);
    /// Niche Option<&T>: the single pointer cell at dest offset 0.
    const SBS_TAG_OFF: u64 = 0;

    #[derive(Clone)]
    struct SbsCfg {
        /// Byte offsets of `step_minus_one` / `first_take` / the `{ptr, end}`
        /// cursor.
        sm_off: u64,
        ft_off: u64,
        src_off: u64,
        /// The EMITTED element stride in bytes (the `Mul` is skipped when 1 —
        /// `emit_element_addr`'s identity simplification).
        stride: u64,
        /// The elem_size the OBLIGATIONS are built with (== `stride` for a
        /// correct emission; different = the wrong-stride bug).
        spec_elem_size: u64,
        /// The `first_take` update mode (shared with the v1 fixture).
        ft_mode: SbFtMode,
        /// Emit the `first_take` store at all (`false` = dropped write-back).
        emit_ft_store: bool,
        /// The niche `Select` yields the PRE-advance `y_ptr` (`false` = the
        /// ADVANCED pointer, the post-increment-yield bug).
        niche_is_y_ptr: bool,
        /// The `None` niche constant (0 = the correct null; nonzero = the
        /// non-null-None bug).
        none_niche: i128,
        /// Defect-1 shape: the niche RELOADS `(self, src_off)` AFTER the
        /// cursor write-back store. The fold must bail (load-after-store).
        niche_reloads_ptr: bool,
    }

    impl SbsCfg {
        /// The correct emission with the canonical layout
        /// `{ Iter { ptr @ 0, end @ 8 }, step_minus_one @ 16, first_take @ 24 }`
        /// and an 8-byte element.
        fn correct() -> Self {
            Self {
                sm_off: 16,
                ft_off: 24,
                src_off: 0,
                stride: 8,
                spec_elem_size: 8,
                ft_mode: SbFtMode::Cleared,
                emit_ft_store: true,
                niche_is_y_ptr: true,
                none_niche: 0,
                niche_reloads_ptr: false,
            }
        }
    }

    /// `emit_element_addr(base, index, stride)` exactly as emitted: the
    /// `coerce_to_plain_ptr` `Copy`, the `PtrToInt`, the `coerce_to_i64`
    /// `Copy` of the index, the `Mul` by the stride CONST (SKIPPED when
    /// stride == 1 — the identity simplification), the `Add`, and the
    /// `IntToPtr`.
    fn sbs_element_addr(
        nodes: &mut Vec<InstrNode>,
        next: &mut u32,
        base: ValueId,
        index: ValueId,
        stride: u64,
    ) -> ValueId {
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        let base_ptr = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::Ptr,
                operand: base,
            },
            base_ptr,
        ));
        let base_int = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: base_ptr,
            },
            base_int,
        ));
        let index_i64 = fresh(next);
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::I64,
                operand: index,
            },
            index_i64,
        ));
        let offset = if stride == 1 {
            index_i64
        } else {
            let size_c = fresh(next);
            nodes.push(node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(stride as i128),
                },
                size_c,
            ));
            let offset = fresh(next);
            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: TrustIrBinOp::Mul,
                    ty: TrustIrTy::I64,
                    lhs: index_i64,
                    rhs: size_c,
                })
                .with_result(offset),
            );
            offset
        };
        let addr_int = fresh(next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Add,
                ty: TrustIrTy::I64,
                lhs: base_int,
                rhs: offset,
            })
            .with_result(addr_int),
        );
        let addr = fresh(next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: addr_int,
            },
            addr,
        ));
        addr
    }

    /// `emit_ptr_to_int(ptr)` exactly as emitted: the `coerce_to_plain_ptr`
    /// `Copy` then the `PtrToInt`.
    fn sbs_ptr_to_int(nodes: &mut Vec<InstrNode>, next: &mut u32, ptr: ValueId) -> ValueId {
        let plain = ValueId::new(*next);
        *next += 1;
        nodes.push(node(
            Inst::Copy {
                ty: TrustIrTy::Ptr,
                operand: ptr,
            },
            plain,
        ));
        let int = ValueId::new(*next);
        *next += 1;
        nodes.push(node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::I64,
                operand: plain,
            },
            int,
        ));
        int
    }

    fn sbs_emit(cfg: &SbsCfg) -> Vec<InstrNode> {
        let mut nodes = Vec::new();
        let mut next = 500u32;
        let fresh = |next: &mut u32| {
            let v = ValueId::new(*next);
            *next += 1;
            v
        };
        // 1. zero = Const 0; the sm/ft address chains; the STD prelude
        //    (IDENTICAL to v1): sm I64 load, ft I8 NARROW load, ZExt, Ne,
        //    countdown Select.
        let zero_c = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(0),
            },
            zero_c,
        ));
        let state_addr = sb_field_addr(&mut nodes, &mut next, SBS_SELF, cfg.sm_off);
        let ft_addr = sb_field_addr(&mut nodes, &mut next, SBS_SELF, cfg.ft_off);
        let sm = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I64,
                ptr: state_addr,
                volatile: false,
                align: None,
            },
            sm,
        ));
        let ft_i8 = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::I8,
                ptr: ft_addr,
                volatile: false,
                align: None,
            },
            ft_i8,
        ));
        let ft = fresh(&mut next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: TrustIrTy::I8,
                dst_ty: TrustIrTy::I64,
                operand: ft_i8,
            },
            ft,
        ));
        let ft_nz = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: TrustIrTy::I64,
                lhs: ft,
                rhs: zero_c,
            })
            .with_result(ft_nz),
        );
        let countdown = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I64,
                cond: ft_nz,
                then_val: zero_c,
                else_val: sm,
            })
            .with_result(countdown),
        );
        // 2. ptr / end Ptr loads.
        let ptr_addr = sb_field_addr(&mut nodes, &mut next, SBS_SELF, cfg.src_off);
        let ptr = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::Ptr,
                ptr: ptr_addr,
                volatile: false,
                align: None,
            },
            ptr,
        ));
        let end_addr = sb_field_addr(&mut nodes, &mut next, SBS_SELF, cfg.src_off + 8);
        let end = fresh(&mut next);
        nodes.push(node(
            Inst::Load {
                ty: TrustIrTy::Ptr,
                ptr: end_addr,
                volatile: false,
                align: None,
            },
            end,
        ));
        // 3. y_ptr = element_addr(ptr, countdown, stride); one = Const 1;
        //    advanced = element_addr(y_ptr, one, stride).
        let y_ptr = sbs_element_addr(&mut nodes, &mut next, ptr, countdown, cfg.stride);
        let one_idx = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(1),
            },
            one_idx,
        ));
        let advanced = sbs_element_addr(&mut nodes, &mut next, y_ptr, one_idx, cfg.stride);
        // 4. PtrToInt x3; UNSIGNED guards + Bool And.
        let ptr_int = sbs_ptr_to_int(&mut nodes, &mut next, ptr);
        let end_int = sbs_ptr_to_int(&mut nodes, &mut next, end);
        let y_int = sbs_ptr_to_int(&mut nodes, &mut next, y_ptr);
        let no_overflow = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Uge,
                ty: TrustIrTy::I64,
                lhs: y_int,
                rhs: ptr_int,
            })
            .with_result(no_overflow),
        );
        let in_range = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: TrustIrTy::I64,
                lhs: y_int,
                rhs: end_int,
            })
            .with_result(in_range),
        );
        let cond = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::And,
                ty: TrustIrTy::Bool,
                lhs: no_overflow,
                rhs: in_range,
            })
            .with_result(cond),
        );
        // 5. new_ptr = Select(Ptr, cond, advanced, ptr); Store(Ptr @ src_off)
        //    — STORE 1 (cursor).
        let new_ptr = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::Ptr,
                cond,
                then_val: advanced,
                else_val: ptr,
            })
            .with_result(new_ptr),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::Ptr,
            ptr: ptr_addr,
            value: new_ptr,
            volatile: false,
            align: None,
        }));
        // 6. ft update exactly as v1 — STORE 2 (first_take, WIDTH 1).
        if cfg.emit_ft_store {
            let new_ft = match cfg.ft_mode {
                SbFtMode::Cleared => {
                    let new_ft = fresh(&mut next);
                    nodes.push(
                        InstrNode::new(Inst::Select {
                            ty: TrustIrTy::I64,
                            cond,
                            then_val: zero_c,
                            else_val: ft,
                        })
                        .with_result(new_ft),
                    );
                    new_ft
                }
                SbFtMode::NotCleared => ft,
                SbFtMode::Unconditional => zero_c,
            };
            let new_ft8 = fresh(&mut next);
            nodes.push(node(
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: TrustIrTy::I64,
                    dst_ty: TrustIrTy::I8,
                    operand: new_ft,
                },
                new_ft8,
            ));
            nodes.push(InstrNode::new(Inst::Store {
                ty: TrustIrTy::I8,
                ptr: ft_addr,
                value: new_ft8,
                volatile: false,
                align: None,
            }));
        }
        // 7. `store_option_some_value` Reference/NICHE arm: none Const +
        //    IntToPtr, Select(Ptr, cond, y_ptr, none), Store(Ptr @ (dest, 0))
        //    — STORE 3 (the whole observable Option).
        let none_int = fresh(&mut next);
        nodes.push(node(
            Inst::Const {
                ty: TrustIrTy::I64,
                value: Constant::Int(cfg.none_niche),
            },
            none_int,
        ));
        let none_ptr = fresh(&mut next);
        nodes.push(node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: TrustIrTy::I64,
                dst_ty: TrustIrTy::Ptr,
                operand: none_int,
            },
            none_ptr,
        ));
        // Defect-1 shape: RELOAD the just-written cursor cell and yield THAT.
        let some_val = if cfg.niche_reloads_ptr {
            let reloaded = fresh(&mut next);
            nodes.push(node(
                Inst::Load {
                    ty: TrustIrTy::Ptr,
                    ptr: ptr_addr,
                    volatile: false,
                    align: None,
                },
                reloaded,
            ));
            reloaded
        } else if cfg.niche_is_y_ptr {
            y_ptr
        } else {
            advanced
        };
        let chosen = fresh(&mut next);
        nodes.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::Ptr,
                cond,
                then_val: some_val,
                else_val: none_ptr,
            })
            .with_result(chosen),
        );
        nodes.push(InstrNode::new(Inst::Store {
            ty: TrustIrTy::Ptr,
            ptr: SBS_DEST,
            value: chosen,
            volatile: false,
            align: None,
        }));
        nodes
    }

    fn sbs_obligations(name: &str, cfg: &SbsCfg) -> Option<Vec<ProofObligation>> {
        let folded =
            fold_emitted_step_by_next(&sbs_emit(cfg)).expect("slice StepBy::next in slice");
        step_by_next_slice_obligations(
            name,
            &folded,
            SBS_SELF,
            SBS_DEST,
            cfg.sm_off,
            cfg.ft_off,
            cfg.src_off,
            cfg.spec_elem_size,
            SBS_TAG_OFF,
        )
    }

    fn sbs_discharge(name: &str, cfg: &SbsCfg) -> RefinementOutcome {
        use trust_cg_verify::ay_bridge::AYConfig;
        use trust_cg_verify::mir_semantics::discharge_refinement;
        let obligations =
            sbs_obligations(name, cfg).expect("slice StepBy::next obligations built");
        let config = AYConfig::default();
        let mut inconclusive = None;
        for ob in &obligations {
            match discharge_refinement(ob, &config) {
                RefinementOutcome::Refined => {}
                r @ RefinementOutcome::Refuted { .. } => return r,
                i @ RefinementOutcome::Inconclusive { .. } => {
                    if inconclusive.is_none() {
                        inconclusive = Some(i);
                    }
                }
            }
        }
        inconclusive.unwrap_or(RefinementOutcome::Refined)
    }

    /// The fold reconstructs the three stored values as EXACTLY the slice
    /// spec formulas (over the same pre-state load symbols — the NARROW
    /// `first_take` load's masked formula and the stride `Mul` included) for
    /// a correct stride-8 emission.
    #[test]
    fn fold_reconstructs_step_by_next_slice() {
        let cfg = SbsCfg::correct();
        let folded = fold_emitted_step_by_next(&sbs_emit(&cfg)).expect("in slice");
        let spec = step_by_next_slice_spec(
            &ld_value_name(SBS_SELF, cfg.sm_off),
            &ld_value_name_w(SBS_SELF, cfg.ft_off, 1),
            &ld_value_name(SBS_SELF, cfg.src_off),
            &ld_value_name(SBS_SELF, cfg.src_off + 8),
            cfg.spec_elem_size,
        );
        assert_eq!(
            folded.store_value(SBS_SELF, cfg.src_off).unwrap(),
            spec.new_ptr
        );
        // The ft store folds to the Trunc-masked value; the spec's `new_ft`
        // carries the same explicit mask.
        assert_eq!(folded.store_value(SBS_SELF, cfg.ft_off).unwrap(), spec.new_ft);
        assert_eq!(folded.store_value(SBS_DEST, SBS_TAG_OFF).unwrap(), spec.niche);
    }

    /// POSITIVE: a correct stride-8 slice `StepBy::next` is NOT refuted.
    #[test]
    fn correct_step_by_next_slice_is_not_refuted() {
        let outcome = sbs_discharge("sbs_correct", &SbsCfg::correct());
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct slice StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// POSITIVE: a correct STRIDE-1 emission (`&[u8]` — `emit_element_addr`
    /// SKIPS the `Mul` by 1, the identity simplification) is NOT refuted
    /// against the spec's `countdown*1` formula.
    #[test]
    fn correct_step_by_next_slice_stride1_mul_skip_is_not_refuted() {
        let cfg = SbsCfg {
            stride: 1,
            spec_elem_size: 1,
            ..SbsCfg::correct()
        };
        let outcome = sbs_discharge("sbs_stride1", &cfg);
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct Mul-skipped stride-1 slice StepBy::next must not be refuted, got {outcome:?}"
        );
        if trust_cg_verify::ay_bridge::z3_available() {
            if alethe_crosscheck_gap(&outcome) {
                eprintln!("{ALETHE_GAP_SKIP_NOTICE}");
                return;
            }
            assert!(matches!(outcome, RefinementOutcome::Refined), "got {outcome:?}");
        }
    }

    /// ANTI-TAUTOLOGY: POST-INCREMENT NICHE — the `Some` arm yields the
    /// ADVANCED pointer (`y_ptr + stride`, an off-by-one-ELEMENT read)
    /// -> REFUTED.
    #[test]
    fn post_increment_niche_step_by_next_slice_is_refuted() {
        let cfg = SbsCfg {
            niche_is_y_ptr: false,
            ..SbsCfg::correct()
        };
        let outcome = sbs_discharge("sbs_post_inc", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a post-increment niche must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: NON-NULL `None` — the `None` niche constant is 1 (an
    /// exhausted pull would decode `Some(&*1)`) -> REFUTED.
    #[test]
    fn non_null_none_step_by_next_slice_is_refuted() {
        let cfg = SbsCfg {
            none_niche: 1,
            ..SbsCfg::correct()
        };
        let outcome = sbs_discharge("sbs_nonnull_none", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a non-null None niche must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: FIRST_TAKE NEVER CLEARED — `new_ft = ft` (the iterator
    /// re-yields element 0 forever) -> REFUTED on the low-byte compare.
    #[test]
    fn ft_not_cleared_step_by_next_slice_is_refuted() {
        let cfg = SbsCfg {
            ft_mode: SbFtMode::NotCleared,
            ..SbsCfg::correct()
        };
        let outcome = sbs_discharge("sbs_ft_not_cleared", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a never-cleared first_take must be REFUTED, got {outcome:?}"
        );
    }

    /// ANTI-TAUTOLOGY: WRONG STRIDE — the emission scales by 16 while the
    /// element is 8 bytes (every step lands one ELEMENT too far; the advance
    /// oversteps) -> REFUTED.
    #[test]
    fn wrong_stride_step_by_next_slice_is_refuted() {
        let cfg = SbsCfg {
            stride: 16,
            spec_elem_size: 8,
            ..SbsCfg::correct()
        };
        let outcome = sbs_discharge("sbs_wrong_stride", &cfg);
        assert!(
            matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a mis-scaled stride must be REFUTED, got {outcome:?}"
        );
    }

    /// SHAPE CHECK: the `first_take` store is DROPPED entirely. Only two
    /// stores fold -> obligations `None` (skip, sound).
    #[test]
    fn missing_ft_store_step_by_next_slice_is_out_of_shape() {
        let cfg = SbsCfg {
            emit_ft_store: false,
            ..SbsCfg::correct()
        };
        assert!(
            sbs_obligations("sbs_no_ft", &cfg).is_none(),
            "a dropped first_take store must fail the exact-store-set shape check"
        );
    }

    /// DEFECT-1 REGRESSION (the lane-7 load-after-store class): the niche
    /// RELOADS the just-written cursor cell after the write-back — the
    /// machine yields the ADVANCED pointer on the yield edge (the
    /// post-increment bug via reload). The fold must BAIL, never bind the
    /// reload to the pre-state symbol.
    #[test]
    fn reload_after_writeback_niche_step_by_next_slice_is_out_of_slice() {
        let cfg = SbsCfg {
            niche_reloads_ptr: true,
            ..SbsCfg::correct()
        };
        assert!(
            fold_emitted_step_by_next(&sbs_emit(&cfg)).is_none(),
            "a niche reloading the written-back cursor cell must be out of slice \
             (load-after-store binds no pre-state symbol)"
        );
    }

    /// SHIFT-UB REGRESSION (lane-12 adversarial finding, solver-CONFIRMED
    /// false-certificate before the fix): trust-ir's authoritative interpreter
    /// (interpret.rs shift_amount) makes a shift amount >= the bit width UB —
    /// NOT a mod-64 wrap (the trust-cg-codegen interpreter's divergent
    /// behavior the original fold arm cited). A packed emission shifting by 96
    /// is UB IR that any verified pass may transform arbitrarily; the fold
    /// must BAIL (skip, never certify). Mutates the correct packed emission's
    /// shift constants 32 -> 96.
    #[test]
    fn oversized_shift_step_by_next_packed_is_out_of_slice() {
        let mut nodes = sbp_emit(&SbpCfg::correct());
        let mut mutated = 0usize;
        for n in nodes.iter_mut() {
            if let Inst::Const {
                value: Constant::Int(v),
                ..
            } = &mut n.inst
            {
                if *v == 32 {
                    *v = 96;
                    mutated += 1;
                }
            }
        }
        assert!(mutated >= 1, "expected to find the shift-amount Const 32");
        assert!(
            fold_emitted_step_by_next(&nodes).is_none(),
            "a shift by >= 64 is UB IR and must be out of the fold slice \
             (skip-not-certify; the mod-64 model was a confirmed false-certificate)"
        );
    }

    // -----------------------------------------------------------------------
    // TV lane 14 — slice-to-Vec `{ptr, cap, len}` header fold
    // -----------------------------------------------------------------------

    const TV_SLOT: ValueId = ValueId::new(200);
    const TV_ONE: ValueId = ValueId::new(201);
    const TV_GT: ValueId = ValueId::new(202);
    const TV_CAP: ValueId = ValueId::new(203);
    const TV_SIZE: ValueId = ValueId::new(204);
    const TV_BYTES: ValueId = ValueId::new(205);
    const TV_ALIGN: ValueId = ValueId::new(206);
    const TV_DATA: ValueId = ValueId::new(207);
    const TV_N: ValueId = ValueId::new(208); // external: the source element count
    const TV_OTHER: ValueId = ValueId::new(209); // an unrelated base

    const VEC_PTR: u32 = 0;
    const VEC_CAP: u32 = 1;
    const VEC_LEN: u32 = 2;

    /// The EXACT 11-node header window `lower_slice_to_vec` emits.
    fn tv_header(elem_size: i128, elem_align: i128) -> Vec<InstrNode> {
        vec![
            node(
                Inst::Alloca {
                    ty: TrustIrTy::I64,
                    count: None,
                    align: None,
                },
                TV_SLOT,
            ),
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(1),
                },
                TV_ONE,
            ),
            node(
                Inst::ICmp {
                    op: ICmpOp::Ugt,
                    ty: TrustIrTy::I64,
                    lhs: TV_N,
                    rhs: TV_ONE,
                },
                TV_GT,
            ),
            node(
                Inst::Select {
                    ty: TrustIrTy::I64,
                    cond: TV_GT,
                    then_val: TV_N,
                    else_val: TV_ONE,
                },
                TV_CAP,
            ),
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(elem_size),
                },
                TV_SIZE,
            ),
            node(
                Inst::BinOp {
                    op: TrustIrBinOp::Mul,
                    ty: TrustIrTy::I64,
                    lhs: TV_CAP,
                    rhs: TV_SIZE,
                },
                TV_BYTES,
            ),
            node(
                Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(elem_align),
                },
                TV_ALIGN,
            ),
            node(
                Inst::Call {
                    callee: trust_cg_lower::trust_ir_compat::FuncId::new(0),
                    args: vec![TV_BYTES, TV_ALIGN],
                },
                TV_DATA,
            ),
            node(
                Inst::InsertField {
                    ty: TrustIrTy::I64,
                    aggregate: TV_SLOT,
                    field: VEC_PTR,
                    value: TV_DATA,
                },
                ValueId::new(210),
            ),
            node(
                Inst::InsertField {
                    ty: TrustIrTy::I64,
                    aggregate: TV_SLOT,
                    field: VEC_CAP,
                    value: TV_CAP,
                },
                ValueId::new(211),
            ),
            node(
                Inst::InsertField {
                    ty: TrustIrTy::I64,
                    aggregate: TV_SLOT,
                    field: VEC_LEN,
                    value: TV_N,
                },
                ValueId::new(212),
            ),
        ]
    }

    #[test]
    fn tv14_folds_the_real_header_window() {
        let folded = fold_emitted_slice_to_vec_header(&tv_header(4, 4))
            .expect("the real 11-node header window must fold");
        assert_eq!(folded.alloc_result, TV_DATA);
        // The ptr field must record the ALLOCATION's result, not some other
        // pointer — this is the "header stored to a stale base" mutant's target.
        assert!(folded.store_value(VEC_PTR).is_some());
        assert!(folded.store_value(VEC_CAP).is_some());
        assert!(folded.store_value(VEC_LEN).is_some());
    }

    /// SHAPE PIN. The panel's finding was that every structural wrong emission
    /// otherwise degrades to a SILENT SKIP indistinguishable from "not a
    /// to_vec". Dropping any node must be refused by the length pin.
    #[test]
    fn tv14_shape_drift_is_refused_not_silently_skipped() {
        for drop_idx in [0usize, 3, 7, 10] {
            let mut nodes = tv_header(4, 4);
            nodes.remove(drop_idx);
            assert!(
                fold_emitted_slice_to_vec_header(&nodes).is_none(),
                "a {}-node window must be refused by the shape pin (dropped idx {drop_idx})",
                nodes.len()
            );
        }
    }

    /// A header field written into a DIFFERENT base than the `Alloca` slot must
    /// refuse — the brief's own named mutant.
    #[test]
    fn tv14_store_to_stale_base_is_refused() {
        let mut nodes = tv_header(4, 4);
        if let Inst::InsertField { aggregate, .. } = &mut nodes[9].inst {
            *aggregate = TV_OTHER;
        } else {
            panic!("node 9 must be the cap InsertField");
        }
        assert!(
            fold_emitted_slice_to_vec_header(&nodes).is_none(),
            "a header field stored to a foreign base must be refused"
        );
    }

    /// Two stores into the SAME field (so one header field is never written)
    /// must refuse — the D4 pairwise-distinct check.
    #[test]
    fn tv14_duplicate_field_store_is_refused() {
        let mut nodes = tv_header(4, 4);
        if let Inst::InsertField { field, .. } = &mut nodes[10].inst {
            *field = VEC_CAP; // len store overwrites cap; len never written
        } else {
            panic!("node 10 must be the len InsertField");
        }
        assert!(
            fold_emitted_slice_to_vec_header(&nodes).is_none(),
            "duplicate header field stores must be refused (D4)"
        );
    }

    /// The fold must read the alloc size/align from the ACTUAL call arguments,
    /// so a different emitted element size yields a different folded value —
    /// which is what makes the obligation against the spec refutational rather
    /// than an identity.
    #[test]
    fn tv14_alloc_size_is_read_from_the_emission() {
        let a = fold_emitted_slice_to_vec_header(&tv_header(4, 4)).expect("folds");
        let b = fold_emitted_slice_to_vec_header(&tv_header(8, 4)).expect("folds");
        assert_ne!(
            format!("{:?}", a.alloc_bytes),
            format!("{:?}", b.alloc_bytes),
            "a different emitted elem_size must fold to a different byte count"
        );
        let c = fold_emitted_slice_to_vec_header(&tv_header(4, 16)).expect("folds");
        assert_ne!(
            format!("{:?}", a.alloc_align),
            format!("{:?}", c.alloc_align),
            "a different emitted alignment must fold to a different align value"
        );
    }
}
