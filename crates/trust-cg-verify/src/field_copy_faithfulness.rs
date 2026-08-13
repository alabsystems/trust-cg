//! Faithfulness gate for a field-wise aggregate copy.
//!
//! The MIR -> trust-ir frontend lowers a whole-aggregate copy between a SCALARIZED
//! local (per-field SSA bindings) and a MEMORY-backed local (a stack slot) as a
//! sequence of per-field typed loads/stores at byte offsets. Each individual
//! load/store is discharged by the per-instruction lowering-proof certificates, but
//! those proofs are blind to the COMPOSITION: they prove "this Store is a correct
//! Store", not "this *set* of Stores faithfully reproduces aggregate `S`". The
//! composition is the trusted-frontend boundary.
//!
//! This module closes that class with an independent, fail-closed check: given the
//! copy plan the emitter will actually run (one byte span per field) and the rustc
//! layout's field offsets+sizes (an INDEPENDENT ground truth), it verifies the plan
//! exactly tiles the aggregate's fields — one span per field, each at its layout
//! offset covering its full size (no partial / over-wide leaf access, which would
//! copy the wrong bytes), pairwise disjoint (no field clobbering another). Any
//! deviation means the lowering would copy the wrong bytes, so the caller fails the
//! compile CLOSED rather than miscompiling.
//!
//! It is the per-FIELD analogue of the existing whole-copy `layout.size % lane_size`
//! coverage assert, and binds the emitter's per-field leaf-type choice
//! (`memory_scalar_leaf_ty`) to the layout, exactly the "translation-validate an
//! emitter choice against an independent primitive" pattern the carrier / guard
//! validators use.

/// One field's byte coverage in a field-wise aggregate copy: the byte `offset`
/// within the aggregate slot and the number of bytes (`size`) the access covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldCopySpan {
    pub offset: u64,
    pub size: u64,
}

impl FieldCopySpan {
    pub fn new(offset: u64, size: u64) -> Self {
        FieldCopySpan { offset, size }
    }

    fn end(&self) -> u64 {
        self.offset.saturating_add(self.size)
    }
}

/// Verify that `plan` (what the emitter will load/store, one span per field, in
/// field order) faithfully tiles `layout_fields` (the rustc field offsets+sizes for
/// the same aggregate, in the same field order).
///
/// Returns `Ok(())` iff every field is copied exactly once, at its layout offset,
/// covering its full layout size, with no two spans overlapping. Otherwise returns
/// an `Err` describing the first violation — the caller treats this as a
/// fail-closed compile error (the copy would reproduce the wrong bytes).
pub fn verify_field_copy_tiling(
    plan: &[FieldCopySpan],
    layout_fields: &[FieldCopySpan],
) -> Result<(), String> {
    if plan.len() != layout_fields.len() {
        return Err(format!(
            "field-copy faithfulness: plan covers {} field(s) but the layout has {}",
            plan.len(),
            layout_fields.len()
        ));
    }
    for (i, (p, l)) in plan.iter().zip(layout_fields.iter()).enumerate() {
        if p.offset != l.offset {
            return Err(format!(
                "field-copy faithfulness: field {i} is copied at byte offset {} but its \
                 layout offset is {} (would read/write the wrong bytes)",
                p.offset, l.offset
            ));
        }
        if p.size != l.size {
            return Err(format!(
                "field-copy faithfulness: field {i} uses a {}-byte access but its layout \
                 field is {} byte(s) (a partial / over-wide copy)",
                p.size, l.size
            ));
        }
    }
    // Pairwise-disjoint check: no field's byte range may overlap another's (which
    // would clobber or alias a sibling field). Sort the spans and check neighbors.
    let mut spans: Vec<(u64, u64)> = plan.iter().map(|s| (s.offset, s.end())).collect();
    spans.sort_unstable();
    for w in spans.windows(2) {
        if w[0].1 > w[1].0 {
            return Err(format!(
                "field-copy faithfulness: field byte ranges overlap ([{}, {}) and [{}, {}))",
                w[0].0, w[0].1, w[1].0, w[1].1
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // A faithful 16-byte struct { a: i64 @0, b: i64 @8 }.
    fn struct16_layout() -> Vec<FieldCopySpan> {
        vec![FieldCopySpan::new(0, 8), FieldCopySpan::new(8, 8)]
    }

    // A reorder-prone { a: i8 @0, b: i64 @8 } (7 padding bytes at 1..8 NOT copied —
    // padding is don't-care, only field bytes are part of the value).
    fn reorder_layout() -> Vec<FieldCopySpan> {
        vec![FieldCopySpan::new(0, 1), FieldCopySpan::new(8, 8)]
    }

    #[test]
    fn accepts_faithful_tiling() {
        let layout = struct16_layout();
        assert!(verify_field_copy_tiling(&layout.clone(), &layout).is_ok());
    }

    #[test]
    fn accepts_padded_reorder_tiling() {
        let layout = reorder_layout();
        // The plan copies each FIELD exactly (padding bytes are not part of the value).
        assert!(verify_field_copy_tiling(&layout.clone(), &layout).is_ok());
    }

    #[test]
    fn rejects_partial_field_copy() {
        // A leaf type too NARROW for the field (e.g. an I32 access on an I64 field):
        // field 0 copies only 4 of its 8 bytes -> 4 bytes silently dropped.
        let plan = vec![FieldCopySpan::new(0, 4), FieldCopySpan::new(8, 8)];
        let err = verify_field_copy_tiling(&plan, &struct16_layout()).unwrap_err();
        assert!(err.contains("field 0"), "got: {err}");
        assert!(err.contains("partial"), "got: {err}");
    }

    #[test]
    fn rejects_overwide_field_copy() {
        // A leaf type too WIDE for the field would read/write into the neighbor.
        let plan = vec![FieldCopySpan::new(0, 16), FieldCopySpan::new(8, 8)];
        assert!(verify_field_copy_tiling(&plan, &struct16_layout()).is_err());
    }

    #[test]
    fn rejects_wrong_offset() {
        // Field 1 written at the wrong offset (4 instead of its layout 8): the two
        // fields would now overlap AND field 1 lands in the wrong place.
        let plan = vec![FieldCopySpan::new(0, 8), FieldCopySpan::new(4, 8)];
        assert!(verify_field_copy_tiling(&plan, &struct16_layout()).is_err());
    }

    #[test]
    fn rejects_missing_field() {
        // The plan dropped a field entirely (count mismatch).
        let plan = vec![FieldCopySpan::new(0, 8)];
        let err = verify_field_copy_tiling(&plan, &struct16_layout()).unwrap_err();
        assert!(
            err.contains("1 field(s) but the layout has 2"),
            "got: {err}"
        );
    }

    #[test]
    fn rejects_overlapping_spans() {
        // Two same-count spans whose byte ranges overlap (would clobber each other),
        // matched 1:1 to a layout that (hypothetically) placed them disjoint.
        let plan = vec![FieldCopySpan::new(0, 8), FieldCopySpan::new(4, 8)];
        let layout = vec![FieldCopySpan::new(0, 8), FieldCopySpan::new(4, 8)];
        // offset matches here, but the spans overlap -> rejected by the disjoint check.
        let err = verify_field_copy_tiling(&plan, &layout).unwrap_err();
        assert!(err.contains("overlap"), "got: {err}");
    }
}
