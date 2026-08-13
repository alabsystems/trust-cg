// crates/rustc-codegen-trust-cg/src/place_resolution_weld.rs
//
// Phase P2b (differential WELD) — the place-resolution DISPATCH kernel proven sound.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This module WELDS the REAL, TyCtxt-free dispatch kernel `resolve_place_kernel`
// (crate root, extracted in Phase P2a) to an INDEPENDENT re-encoding of the
// machine-checked Lean model in `proofs/mir_place_resolution_spec.lean`. The
// test `resolve_place_kernel_agrees_with_lean_model_over_full_finite_domain`
// enumerates the ENTIRE finite `(ProjShape × BindingFlags)` domain and asserts
// the kernel and the model-derived oracle agree at EVERY point.
//
// ANTI-COLLUSION. `oracle_resolve` below is written FROM the Lean spec's nested
// `match` (proofs/mir_place_resolution_spec.lean `def resolvePlace`), NOT copied
// from `resolve_place_kernel`. It shares NO helper with the kernel: it re-derives
// `is_zero` (`oracle_is_f0`), the `unwrap_or(F0)` default (`oracle_unwrap_tag`),
// the `newtype_passthrough` predicate (`oracle_npass`), and the shared Index arm
// (`oracle_resolve_indexed`) from the spec independently. The kernel writes its
// Empty guard as one `!scalar_value && has_proj_any` conjunction; the oracle,
// mirroring the Lean nested match, splits it into sequential `scalar_value` /
// `has_proj_any` cases — so a routing regression in the kernel (a wrong gate
// order, a flipped condition, an off-by-one field key) makes the two disagree.
//
// RESIDUAL TCB (mirrors the header of mir_place_resolution_spec.lean — the
// abstraction seams this weld does NOT close):
//   (a) READ_BINDING_FLAGS FAITHFULNESS. The weld drives `resolve_place_kernel`
//       with SYNTHETIC `BindingFlags` covering every combination; that the real
//       `read_binding_flags` (lib.rs:44692-44727) computes each flag from the
//       actual ctx map lookups is the abstraction↔real glue and stays trusted.
//   (b) FINITE-DOMAIN-COVERS-REALITY. `classify_place_shape` collapses every real
//       projection chain to a `ProjShape` variant; every unmatched chain maps to
//       `ProjShape::Other`, which both kernel and model always `Reject`. The
//       single `Other ↦ Reject` point here STANDS FOR every unmatched real chain
//       (fail-closed); that the collapse is exhaustive of reality is trusted.
//   (c) VALUE-LOOKUP LAYER IS P1's JOB. This kernel decides the ROUTE only; the
//       value lookups (`value_for_scalar_binding`, `projected_values.get`, the
//       borrowed-scalar target chase) stay in the callers (lib.rs:44797-44821)
//       and are Phase P1's subject. A correct route with a wrong value is not
//       caught here.
//   (d) DOWNCAST+FIELD COLLAPSE IS A MODELING CHOICE. Both `Field(f)` and
//       `DowncastField(f)` route to `ProjectedField(f)` — the SAME key. This is
//       intentional (same projected-value key `(local, field)`), NOT an
//       off-by-one; the model's `field_downcast_same_key` documents it.

use crate::{
    resolve_place_kernel, BindingFlags, DerefTarget, DerefTargetKind, FieldTag, ProjShape,
    RejectReason, Resolution,
};

// -----------------------------------------------------------------------------
// INDEPENDENT ORACLE HELPERS — each a direct re-encoding of a Lean spec helper,
// NOT a call into any `resolve_place_kernel` helper.
// -----------------------------------------------------------------------------

/// Mirror of Lean `npass` (`(scalar_value || scalar_constant) && !has_proj_any`,
/// spec `def npass`), re-encoded as the spec's nested match — NOT the kernel's
/// `&&`/`||` form.
fn oracle_npass(scalar_value: bool, scalar_constant: bool, has_proj_any: bool) -> bool {
    // Lean: match has_proj_any | yes => no
    //                          | no  => (match scalar_value | yes => yes | no => scalar_constant)
    if has_proj_any {
        false
    } else if scalar_value {
        true
    } else {
        scalar_constant
    }
}

/// Mirror of Lean `isZero` / the `tag.is_zero()` predicate (F0 only), re-derived
/// here rather than calling the kernel's `FieldTag::is_zero`.
fn oracle_is_f0(tag: FieldTag) -> bool {
    match tag {
        FieldTag::F0 => true,
        FieldTag::F1 => false,
        FieldTag::F2 => false,
    }
}

/// Mirror of Lean `unwrapTag` (`field_tag.unwrap_or(F0)`), re-derived by match.
fn oracle_unwrap_tag(field_tag: Option<FieldTag>) -> FieldTag {
    match field_tag {
        None => FieldTag::F0,
        Some(t) => t,
    }
}

/// Mirror of Lean `resolveIndexed` — the shared Index/ConstIndex arm: passthrough
/// only on `!has_proj_field && tag.is_zero() && entry_arg_single_scalar`, else
/// `ProjectedField(tag)`. Never rejects.
fn oracle_resolve_indexed(
    field_tag: Option<FieldTag>,
    has_proj_field: bool,
    entry_arg_single_scalar: bool,
) -> Resolution {
    let tag = oracle_unwrap_tag(field_tag);
    if has_proj_field {
        Resolution::ProjectedField(tag)
    } else if !oracle_is_f0(tag) {
        Resolution::ProjectedField(tag)
    } else if entry_arg_single_scalar {
        Resolution::NewtypePassthrough
    } else {
        // tag == F0 here.
        Resolution::ProjectedField(tag)
    }
}

/// INDEPENDENT ORACLE — a direct re-encoding of the Lean `resolvePlace` nested
/// match (proofs/mir_place_resolution_spec.lean). Same arm order, same
/// fail-closed defaults, same field-key routing. Shares NO helper with
/// `resolve_place_kernel`.
fn oracle_resolve(shape: ProjShape, f: BindingFlags) -> Resolution {
    match shape {
        // Lean `empty` arm: four sequential guards, then ScalarLocal.
        ProjShape::Empty => {
            if f.borrowed_scalar {
                Resolution::Reject(RejectReason::BorrowedScalarNoDeref)
            } else if f.borrowed_aggregate {
                Resolution::Reject(RejectReason::BorrowedAggregateNoDeref)
            } else if f.pointer_metadata {
                Resolution::Reject(RejectReason::PointerMetadataAsScalar)
            } else if f.scalar_value {
                // Lean: match scalar_value | yes => scalarLocal.
                Resolution::ScalarLocal
            } else if f.has_proj_any {
                // Lean: scalar_value=no & has_proj_any=yes => wholeScalarizedAggregate.
                Resolution::Reject(RejectReason::WholeScalarizedAggregate)
            } else {
                Resolution::ScalarLocal
            }
        }
        // Lean `deref` arm.
        ProjShape::Deref => match f.deref {
            DerefTarget::NoBorrow => Resolution::Reject(RejectReason::DerefBeforeBorrow),
            DerefTarget::Borrow { .. } => Resolution::BorrowTarget,
        },
        // Lean `field` arm (entry-arg OR newtype-passthrough can pass F0 through).
        ProjShape::Field(tag) => {
            if f.has_proj_field {
                Resolution::ProjectedField(tag)
            } else if !oracle_is_f0(tag) {
                Resolution::ProjectedField(tag)
            } else if f.entry_arg_single_scalar {
                Resolution::NewtypePassthrough
            } else if oracle_npass(f.scalar_value, f.scalar_constant, f.has_proj_any) {
                Resolution::NewtypePassthrough
            } else {
                // tag == F0 here.
                Resolution::ProjectedField(tag)
            }
        }
        // Lean `downcastField` arm (entry-arg OR newtype-passthrough can pass F0 through —
        // a single-variant single-field enum's `(e as Only).0` reads its bare scalar,
        // mirroring the plain-`field` arm above).
        ProjShape::DowncastField(tag) => {
            if f.has_proj_field {
                Resolution::ProjectedField(tag)
            } else if !oracle_is_f0(tag) {
                Resolution::ProjectedField(tag)
            } else if f.entry_arg_single_scalar {
                Resolution::NewtypePassthrough
            } else if oracle_npass(f.scalar_value, f.scalar_constant, f.has_proj_any) {
                Resolution::NewtypePassthrough
            } else {
                // tag == F0 here.
                Resolution::ProjectedField(tag)
            }
        }
        // Lean `index` / `constIndex` arms (shared resolveIndexed; from_end ignored).
        ProjShape::Index => {
            oracle_resolve_indexed(f.field_tag, f.has_proj_field, f.entry_arg_single_scalar)
        }
        ProjShape::ConstIndex { .. } => {
            oracle_resolve_indexed(f.field_tag, f.has_proj_field, f.entry_arg_single_scalar)
        }
        // Lean `fieldChain` arm.
        ProjShape::FieldChain => {
            if oracle_npass(f.scalar_value, f.scalar_constant, f.has_proj_any) {
                Resolution::NewtypePassthrough
            } else {
                Resolution::Reject(RejectReason::PlaceProjection)
            }
        }
        // Lean `other` arm — the catch-all fail-closed reject.
        ProjShape::Other => Resolution::Reject(RejectReason::PlaceProjection),
    }
}

// -----------------------------------------------------------------------------
// FULL FINITE DOMAIN ENUMERATION.
// -----------------------------------------------------------------------------

/// Every `ProjShape` value (13): Empty, Deref, Field(F0/F1/F2), DowncastField(
/// F0/F1/F2), Index, ConstIndex{from_end: false/true}, FieldChain, Other.
fn all_shapes() -> Vec<ProjShape> {
    let tags = [FieldTag::F0, FieldTag::F1, FieldTag::F2];
    let mut v = vec![ProjShape::Empty, ProjShape::Deref];
    for t in tags {
        v.push(ProjShape::Field(t));
    }
    for t in tags {
        v.push(ProjShape::DowncastField(t));
    }
    v.push(ProjShape::Index);
    v.push(ProjShape::ConstIndex { from_end: false });
    v.push(ProjShape::ConstIndex { from_end: true });
    v.push(ProjShape::FieldChain);
    v.push(ProjShape::Other);
    v
}

/// Every `DerefTarget` value (13): NoBorrow, plus Borrow over 3 kinds × 2
/// mutabilities × 2 branch-varying flags.
fn all_deref() -> Vec<DerefTarget> {
    let mut v = vec![DerefTarget::NoBorrow];
    for kind in [
        DerefTargetKind::LocalSelf,
        DerefTargetKind::LocalOther,
        DerefTargetKind::Projection,
    ] {
        for mutable in [false, true] {
            for branch_varying in [false, true] {
                v.push(DerefTarget::Borrow {
                    kind,
                    mutable,
                    branch_varying,
                });
            }
        }
    }
    v
}

/// Every `field_tag : Option<FieldTag>` value (4): None, Some(F0/F1/F2).
fn all_field_tag() -> [Option<FieldTag>; 4] {
    [
        None,
        Some(FieldTag::F0),
        Some(FieldTag::F1),
        Some(FieldTag::F2),
    ]
}

/// EXHAUSTIVE differential enumeration of `resolve_place_kernel` over the FULL
/// finite `(ProjShape × BindingFlags)` domain, asserting agreement with the
/// INDEPENDENT Lean-model oracle at EVERY point.
///
/// Domain size (no pruning — the full cartesian product, strictly stronger than
/// a shape-relevance-pruned subset):
///   shape(13) × 8 bool flags(2^8 = 256) × field_tag(4) × deref(13)
///   = 13 × 256 × 4 × 13 = 173_056.
#[test]
fn resolve_place_kernel_agrees_with_lean_model_over_full_finite_domain() {
    let shapes = all_shapes();
    let derefs = all_deref();
    let field_tags = all_field_tag();

    assert_eq!(shapes.len(), 13, "expected 13 ProjShape values");
    assert_eq!(derefs.len(), 13, "expected 13 DerefTarget values");

    let mut enumerated: u64 = 0;
    let mut disagreements: Vec<String> = Vec::new();

    for &shape in &shapes {
        // The 8 bool `BindingFlags` fields as a bitmask, one bit each.
        for mask in 0u16..256u16 {
            let borrowed_scalar = (mask & 1) != 0;
            let borrowed_aggregate = (mask & 2) != 0;
            let pointer_metadata = (mask & 4) != 0;
            let scalar_value = (mask & 8) != 0;
            let scalar_constant = (mask & 16) != 0;
            let has_proj_any = (mask & 32) != 0;
            let has_proj_field = (mask & 64) != 0;
            let entry_arg_single_scalar = (mask & 128) != 0;

            for &field_tag in &field_tags {
                for &deref in &derefs {
                    enumerated += 1;

                    let flags = BindingFlags {
                        borrowed_scalar,
                        borrowed_aggregate,
                        pointer_metadata,
                        scalar_value,
                        scalar_constant,
                        has_proj_any,
                        has_proj_field,
                        field_tag,
                        entry_arg_single_scalar,
                        deref,
                    };

                    // (b) the REAL kernel; (c) the INDEPENDENT model oracle.
                    let kernel = resolve_place_kernel(shape, flags);
                    let oracle = oracle_resolve(shape, flags);

                    // (d) assert AGREEMENT; collect any disagreement with coordinates.
                    if kernel != oracle {
                        disagreements.push(format!(
                            "DISAGREEMENT @ shape={shape:?} flags={flags:?}: \
                             kernel={kernel:?} oracle={oracle:?}"
                        ));
                    }
                }
            }
        }
    }

    assert!(
        disagreements.is_empty(),
        "resolve_place_kernel diverged from the Lean model on {} of {} points:\n{}",
        disagreements.len(),
        enumerated,
        disagreements.join("\n")
    );
    // Whole finite (shape × flags) domain enumerated.
    assert_eq!(
        enumerated,
        13 * 256 * 4 * 13,
        "must enumerate the full finite (shape × flags) domain (173_056 points)"
    );
}
