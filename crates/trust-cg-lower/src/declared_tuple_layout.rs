// trust-cg-lower/declared_tuple_layout.rs - admitting v42 declared tuple layouts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Admission of trust-ir v42 declared tuple layouts (`Module.tuple_layouts`)
//! on the LIR byte path (WS7.7).
//!
//! # What the byte path does with a tuple
//!
//! A `Ty::Tuple` lowers to a repr-less `Type::Struct` of its translated
//! elements, in DECLARATION order. Every consumer then reads that carrier's
//! natural-C layout: `StructGep` resolves a field address through
//! `Type::offset_of`, the by-value copy extent and every stack slot are
//! `Type::bytes()`, the ABI classifier sizes it from the same carrier. None of
//! them can express any other layout.
//!
//! # The rule
//!
//! A declared row is ADMITTED only when it EQUALS that recomputation: every
//! field offset, the size and the align. The declared layout is then honoured
//! by construction — each consumer computes exactly the addresses and extents
//! the producer (rustc) stated. A row that differs in any component is REFUSED
//! with [`AdapterError::DeclaredTupleLayoutDisagrees`], naming the first
//! component that differs; it is never substituted, because compiling the
//! tuple at the recomputed layout would disagree with every rustc-compiled
//! view of the same memory (and with this backend's own object writer, which
//! lays a tuple-typed global initializer out at the DECLARED offsets).
//!
//! Honouring a disagreeing row — rustc reorders `repr(Rust)` tuples, so
//! `(u16, u64, u8)` is `u64@0 u16@8 u8@10`, size 16, where declaration order
//! gives size 24 — needs the offset+extent move the struct path made
//! ([`crate::declared_layout`]). That is a follow-up, not this module.
//!
//! A row the trust-ir coherence check rejects (a dangling type id, a
//! non-tuple type, overlapping or misaligned offsets, a missing target stamp)
//! is refused with [`AdapterError::DeclaredTupleLayoutMalformed`] before any
//! comparison: an incoherent table has no layout to agree with.
//!
//! A tuple the table names no row for keeps the declaration-order carrier it
//! always had; that is the same named fallback a module with no table takes.
//!
//! # Census (the from-source producer corpus)
//!
//! Every binary trust-ir module the source-built trustc (5b45b83b8) emitted
//! in the 2026-09-17 two-language proof program
//! (`~/Library/Caches/trust-ir-two-language-proof/verify/`, the c13 and c14
//! lenses, vendored-source copies excluded: 21 `*.trust-ir.bin` modules) was
//! decoded and run through [`admit`] on 2026-09-30, one row at a time and
//! then whole-module: 6 modules carry a table, holding 8 rows. **6 rows
//! agree, 2 disagree**, and both disagreeing rows are in one module (`c14
//! bydesign-out/tup`: `(u16, u64, u8)` and `(u8, u64, u16)`, which rustc
//! reorders to `u64@0`, size 16, where declaration order gives 24). So 5 of
//! the 6 modules are admitted by this rule and 1 is refused by name, where
//! every one of them was refused before. This is a small corpus: the rate on
//! real crates is unmeasured.

use crate::adapter::{AdapterError, translate_type_with_enum_tables};
use crate::types::Type;
use trust_ir::{Module, TupleLayoutDescriptor, Ty};

/// The component of a declared tuple layout that disagrees with the
/// declaration-order recomputation — the `field` of
/// [`AdapterError::DeclaredTupleLayoutDisagrees`].
///
/// Compared in this order; the first difference is the one reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TupleLayoutComponent {
    /// The byte offset of the tuple element at this (logical) index.
    FieldOffset(usize),
    /// The tuple's total size in bytes.
    Size,
    /// The tuple's alignment in bytes.
    Align,
}

impl std::fmt::Display for TupleLayoutComponent {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TupleLayoutComponent::FieldOffset(index) => write!(formatter, "field {index} offset"),
            TupleLayoutComponent::Size => formatter.write_str("size"),
            TupleLayoutComponent::Align => formatter.write_str("align"),
        }
    }
}

/// Test-only mutation: skip the agreement comparison, i.e. substitute the
/// declaration-order layout for a disagreeing declared row — exactly the
/// silent substitution [`admit`] exists to refuse.
#[cfg(feature = "mutation-knobs")]
fn agreement_check_skipped() -> bool {
    crate::mutation_knobs::admit_disagreeing_tuple_layouts()
}

#[cfg(not(feature = "mutation-knobs"))]
fn agreement_check_skipped() -> bool {
    false
}

/// Admit `module`'s declared tuple layouts on the byte path, or refuse by
/// name. See the module documentation for the rule.
///
/// An empty table is admitted without work. A type the byte path cannot
/// translate at all propagates that translation's own error, and a tuple
/// whose carrier is not one struct lane per element is refused as
/// [`AdapterError::DeclaredTupleLayoutUnsupported`]: neither has a
/// recomputation to agree with.
pub fn admit(module: &Module) -> Result<(), AdapterError> {
    if module.tuple_layouts.is_empty() {
        return Ok(());
    }
    module.validate_tuple_layouts().map_err(|error| {
        AdapterError::DeclaredTupleLayoutMalformed {
            module: module.name.clone(),
            reason: error.to_string(),
        }
    })?;
    for descriptor in &module.tuple_layouts {
        admit_row(module, descriptor)?;
    }
    Ok(())
}

fn admit_row(module: &Module, descriptor: &TupleLayoutDescriptor) -> Result<(), AdapterError> {
    // `validate_tuple_layouts` has resolved every row to a `Ty::Tuple`; asked
    // again so this function stands on its own.
    let malformed = |reason: String| AdapterError::DeclaredTupleLayoutMalformed {
        module: module.name.clone(),
        reason,
    };
    let tuple_type = descriptor.tuple_type;
    let ty = module
        .types
        .get(tuple_type.as_usize())
        .ok_or_else(|| malformed(format!("row names missing type ty.{}", tuple_type.index())))?;
    let Ty::Tuple(elements) = ty else {
        return Err(malformed(format!(
            "row names ty.{}, which is not a tuple",
            tuple_type.index()
        )));
    };
    if descriptor.field_offsets.len() != elements.len() {
        return Err(malformed(format!(
            "row for ty.{} states {} offsets for {} elements",
            tuple_type.index(),
            descriptor.field_offsets.len(),
            elements.len()
        )));
    }
    let carrier = translate_type_with_enum_tables(
        ty,
        &module.structs,
        &module.types,
        &module.enums,
        &module.records,
        &module.closure_types,
    )?;
    // A tuple whose carrier is not one struct lane per element (a lane the
    // byte path drops or merges) has no per-field recomputation: the table is
    // coherent, this path simply cannot consume it, so it is refused as
    // unsupported rather than called malformed.
    let emitted = recomputed_layout(&carrier, elements.len()).ok_or_else(|| {
        AdapterError::DeclaredTupleLayoutUnsupported {
            module: module.name.clone(),
            layouts: module.tuple_layouts.len(),
        }
    })?;
    if agreement_check_skipped() {
        return Ok(());
    }
    let declared = descriptor
        .field_offsets
        .iter()
        .copied()
        .enumerate()
        .map(|(index, offset)| (TupleLayoutComponent::FieldOffset(index), offset))
        .chain([
            (TupleLayoutComponent::Size, descriptor.size),
            (TupleLayoutComponent::Align, descriptor.align),
        ]);
    for ((field, declared), (_, emitted)) in declared.zip(emitted) {
        if declared != emitted {
            return Err(AdapterError::DeclaredTupleLayoutDisagrees {
                module: module.name.clone(),
                tuple: ty.to_string(),
                tuple_type: tuple_type.index(),
                field,
                declared,
                emitted,
            });
        }
    }
    Ok(())
}

/// The declaration-order layout of a tuple's `Type::Struct` carrier, in the
/// comparison order: each field offset, then the size, then the align.
fn recomputed_layout(carrier: &Type, fields: usize) -> Option<Vec<(TupleLayoutComponent, u64)>> {
    let Type::Struct(lanes) = carrier else {
        return None;
    };
    if lanes.len() != fields {
        return None;
    }
    let mut layout = Vec::with_capacity(fields + 2);
    for index in 0..fields {
        let offset = carrier.offset_of(index)?;
        layout.push((TupleLayoutComponent::FieldOffset(index), u64::from(offset)));
    }
    layout.push((TupleLayoutComponent::Size, u64::from(carrier.bytes())));
    layout.push((TupleLayoutComponent::Align, u64::from(carrier.align())));
    Some(layout)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};

    fn module_with(elements: Vec<Ty>, size: u64, align: u64, offsets: Vec<u64>) -> Module {
        let mut module = Module::new("declared_tuple_layout_unit");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        let tuple_type = module
            .add_type(Ty::Tuple(elements))
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type,
            size,
            align,
            field_offsets: offsets,
        });
        module
    }

    #[test]
    fn natural_row_is_admitted() {
        admit(&module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![0, 8])).expect("natural row");
        admit(&module_with(vec![Ty::U8, Ty::U64], 16, 8, vec![0, 8])).expect("padded row");
        admit(&Module::new("empty")).expect("no table");
    }

    #[test]
    fn swapped_offsets_are_refused_at_the_first_field() {
        let error = admit(&module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![8, 0]))
            .expect_err("swapped offsets");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    tuple_type: 0,
                    field: TupleLayoutComponent::FieldOffset(0),
                    declared: 8,
                    emitted: 0,
                    ..
                }
            ),
            "{error:?}"
        );
    }

    #[test]
    fn reordered_row_with_a_smaller_size_is_refused() {
        // rustc's `(u16, u64, u8)`: u64@0 u16@8 u8@10, size 16.
        let error = admit(&module_with(
            vec![Ty::U16, Ty::U64, Ty::U8],
            16,
            8,
            vec![8, 0, 10],
        ))
        .expect_err("reordered row");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    field: TupleLayoutComponent::FieldOffset(0),
                    declared: 8,
                    emitted: 0,
                    ..
                }
            ),
            "{error:?}"
        );
    }

    #[test]
    fn a_padded_size_alone_is_refused_as_the_size() {
        // Offsets agree, but the declared size is one alignment step larger
        // than the carrier the slots and copies are sized from.
        let error =
            admit(&module_with(vec![Ty::U8, Ty::U64], 24, 8, vec![0, 8])).expect_err("padded size");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    field: TupleLayoutComponent::Size,
                    declared: 24,
                    emitted: 16,
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// WS7.7: review — offsets and size agree, only the declared align is
    /// larger: refused at the align, the last component compared.
    #[test]
    fn an_align_only_disagreement_is_refused_as_the_align() {
        let error = admit(&module_with(vec![Ty::U64, Ty::U64], 16, 16, vec![0, 8]))
            .expect_err("over-aligned row");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    field: TupleLayoutComponent::Align,
                    declared: 16,
                    emitted: 8,
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// WS7.7: review — every row is checked, not only the first: an outer
    /// tuple whose row agrees does not admit a disagreeing row for the tuple
    /// nested in it, and the refusal names the INNER tuple.
    #[test]
    fn a_disagreeing_nested_row_is_refused_behind_an_agreeing_outer_row() {
        let inner = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let mut module = module_with(vec![Ty::U8, inner.clone()], 24, 8, vec![0, 8]);
        let inner_type = module
            .add_type(inner)
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: inner_type,
            size: 16,
            align: 8,
            field_offsets: vec![8, 0],
        });
        module
            .validate_tuple_layouts()
            .expect("both rows are coherent");
        let error = admit(&module).expect_err("inner row disagrees");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    tuple_type: 1,
                    field: TupleLayoutComponent::FieldOffset(0),
                    declared: 8,
                    emitted: 0,
                    ..
                }
            ),
            "{error:?}"
        );
        // Control: the same pair with the inner row in declaration order.
        module.tuple_layouts[1].field_offsets = vec![0, 8];
        admit(&module).expect("both rows agree");
    }

    /// WS7.7: review — the byte path lays a packed struct ELEMENT out at its
    /// natural-C extent (`packed_struct_layout`'s known interior divergence),
    /// so a tuple that holds one disagrees with rustc's row and is refused;
    /// the row is never taken on trust for the element's extent.
    #[test]
    fn a_tuple_holding_a_packed_struct_is_refused_at_the_next_field() {
        use trust_ir::{FieldDef, StructDef, StructId, StructRepr};
        let packed = StructId::new(0);
        let mut module = module_with(vec![Ty::U8, Ty::Struct(packed)], 10, 1, vec![0, 1]);
        module.structs.push(StructDef {
            origin: None,
            id: packed,
            name: "Packed".to_string(),
            fields: vec![
                FieldDef {
                    name: "a".to_string(),
                    ty: Ty::U8,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".to_string(),
                    ty: Ty::U64,
                    offset: Some(1),
                },
            ],
            size: Some(9),
            align: Some(1),
            repr: StructRepr::Packed(1),
        });
        // rustc: `#[repr(packed)] Packed { a: u8, b: u64 }` is 9 / 1, so
        // `(u8, Packed)` is `[0, 1]`, size 10, align 1 — coherent here.
        module
            .validate_tuple_layouts()
            .expect("rustc's row is coherent");
        let error = admit(&module).expect_err("packed element");
        assert!(
            matches!(
                error,
                AdapterError::DeclaredTupleLayoutDisagrees {
                    field: TupleLayoutComponent::FieldOffset(1),
                    declared: 1,
                    emitted: 8,
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// WS7.7: review — a 128-bit lane is 16-aligned both in the target's
    /// scalar table and on the LIR carrier, so rustc's natural row for
    /// `(u8, i128)` agrees; an 8-aligned spelling of it is incoherent for
    /// this target (the lane would sit misaligned) and never compared.
    #[test]
    fn a_sixteen_byte_aligned_lane_agrees_only_at_sixteen() {
        admit(&module_with(vec![Ty::U8, Ty::I128], 32, 16, vec![0, 16])).expect("natural i128 row");
        let error = admit(&module_with(vec![Ty::U8, Ty::I128], 24, 8, vec![0, 8]));
        assert!(
            matches!(
                error,
                Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
            ),
            "{error:?}"
        );
    }

    /// WS7.7: review — rows naming a missing type, a non-tuple type, or
    /// stating the wrong number of offsets are malformed, never compared.
    #[test]
    fn rows_naming_no_tuple_or_the_wrong_arity_are_malformed() {
        let mut dangling = module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![0, 8]);
        dangling.tuple_layouts[0].tuple_type = trust_ir::TyId::new(7);
        assert!(matches!(
            admit(&dangling),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
        let mut not_a_tuple = module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![0, 8]);
        not_a_tuple.tuple_layouts[0].tuple_type = not_a_tuple
            .add_type(Ty::U64)
            .expect("Module::add_type: test fixture");
        assert!(matches!(
            admit(&not_a_tuple),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
        let short = module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![0]);
        assert!(matches!(
            admit(&short),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
    }

    #[test]
    fn an_incoherent_table_is_malformed_not_compared() {
        let mut module = module_with(vec![Ty::U64, Ty::U64], 16, 8, vec![0, 0]);
        assert!(matches!(
            admit(&module),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
        module.target_info = None;
        module.tuple_layouts[0].field_offsets = vec![0, 8];
        assert!(matches!(
            admit(&module),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
    }
}
