// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Addressable geometry is not an LIR value representation. Only allocation
//! and whole-pointee GEP may consume these dimensions. The shared IR policy
//! independently refuses every transitive typed SSA/ABI/global/drop use.
use crate::adapter::AdapterError;
use std::cell::RefCell;
use std::collections::HashSet;
use trust_ir::{LayoutTable, Module, Ty};

#[derive(Clone, Copy)]
pub(crate) struct Geometry {
    size_bytes: u64,
    align_bytes: u64,
}
impl Geometry {
    pub(crate) fn size_bytes(self) -> u64 {
        self.size_bytes
    }
    pub(crate) fn stack_slot(self) -> Result<(u32, u32), AdapterError> {
        let size = u32::try_from(self.size_bytes).map_err(|_| {
            AdapterError::UnsupportedType(
                "Storage allocation geometry exceeds the stack-slot size range".into(),
            )
        })?;
        let align = u32::try_from(self.align_bytes).map_err(|_| {
            AdapterError::UnsupportedType(
                "Storage allocation geometry exceeds the stack-slot alignment range".into(),
            )
        })?;
        Ok((size, align))
    }
}

/// One immutable module's shared layout/reach memo, reused for related queries.
/// The exact module pointer is checked before reuse; replacing the adapter's
/// module cannot transfer layout facts. No result grants a typed value.
struct Owner<'a> {
    module: &'a Module,
    table: LayoutTable<'a>,
    unique_declarations: Option<Result<(), String>>,
}
#[derive(Default)]
pub(crate) struct Resolver<'a> {
    table: RefCell<Option<Owner<'a>>>,
}
fn unique_declarations(module: &Module) -> Result<(), String> {
    let mut structs = HashSet::new();
    for row in &module.structs {
        if !structs.insert(row.id) {
            return Err(format!("duplicate struct {:?}", row.id));
        }
    }
    let mut enums = HashSet::new();
    for row in &module.enums {
        if !enums.insert(row.id) {
            return Err(format!("duplicate enum {:?}", row.id));
        }
    }
    let mut records = HashSet::new();
    for row in &module.records {
        if !records.insert(row.id) {
            return Err(format!("duplicate record {:?}", row.id));
        }
    }
    Ok(())
}
impl<'a> Resolver<'a> {
    pub(crate) fn resolve(
        &self,
        module: Option<&'a Module>,
        ty: &Ty,
    ) -> Result<Option<Geometry>, AdapterError> {
        let Some(module) = module else {
            return Ok(None);
        };
        let mut slot = self.table.borrow_mut();
        if slot
            .as_ref()
            .is_none_or(|owner| !std::ptr::eq(owner.module, module))
        {
            *slot = Some(Owner {
                module,
                table: module.layout_table(),
                unique_declarations: None,
            });
        }
        let owner = slot.as_mut().expect("layout owner just installed");
        if !owner.table.type_contains_storage_by_value(ty) {
            return Ok(None);
        }
        // LayoutTable documents first-row lookup for nominal definitions.
        // This new address-only route must not give ambiguous declarations
        // geometry authority merely because one row happened to come first.
        owner
            .unique_declarations
            .get_or_insert_with(|| unique_declarations(module))
            .as_ref()
            .map_err(|detail| {
                AdapterError::UnsupportedType(format!("Storage addressable geometry has {detail}"))
            })?;
        let layout = owner.table.ty_layout_shape(ty).map_err(|error| {
            AdapterError::UnsupportedType(format!(
                "Storage addressable geometry for {ty:?} is unavailable: {error}"
            ))
        })?;
        let size_bytes = layout.size_bytes().ok_or_else(|| {
            AdapterError::UnsupportedType(format!(
                "Storage addressable geometry for {ty:?} is not byte-sized"
            ))
        })?;
        let align_bytes = layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .map(|bits| bits / 8)
            .filter(|align| align.is_power_of_two())
            .ok_or_else(|| {
                AdapterError::UnsupportedType(format!(
                    "Storage addressable geometry for {ty:?} has no byte alignment"
                ))
            })?;
        Ok(Some(Geometry {
            size_bytes,
            align_bytes,
        }))
    }
}

pub(crate) fn admit(module: &Module) -> Result<(), AdapterError> {
    module
        .first_storage_violation()
        .map_or(Ok(()), |violation| {
            Err(AdapterError::StorageNotAdmitted { violation })
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        FieldDef, FuncTy, StorageLayout, StorageViolationKind, StructDef, StructId, StructRepr,
    };
    fn parent(size: u64) -> Module {
        let mut module = Module::new("storage_parent");
        module.structs.push(StructDef {
            id: StructId::new(0),
            name: "Parent".into(),
            origin: None,
            fields: vec![
                FieldDef {
                    name: "head".into(),
                    ty: Ty::U64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "backing".into(),
                    ty: Ty::Storage(StorageLayout::new(80, 8)),
                    offset: Some(8),
                },
                FieldDef {
                    name: "tail".into(),
                    ty: Ty::U64,
                    offset: Some(88),
                },
            ],
            size: Some(size),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        module
    }
    #[test]
    fn exact_parent_geometry_is_not_transferred_between_module_owners() {
        let one = parent(96);
        let two = parent(104);
        let resolver = Resolver::default();
        let ty = Ty::Struct(StructId::new(0));
        for (module, expected) in [(&one, 96), (&two, 104), (&one, 96)] {
            let geometry = resolver.resolve(Some(module), &ty).unwrap().unwrap();
            assert_eq!(geometry.size_bytes, expected);
            assert_eq!(geometry.align_bytes, 8);
        }
    }
    #[test]
    fn parent_missing_overlapping_or_misaligned_offsets_cannot_supply_geometry() {
        for offset in [None, Some(80), Some(89)] {
            let mut module = parent(96);
            module.structs[0].fields[2].offset = offset;
            assert!(
                Resolver::default()
                    .resolve(Some(&module), &Ty::Struct(StructId::new(0)))
                    .is_err()
            );
        }
    }
    #[test]
    fn unused_transitive_abi_is_refused_but_a_pointer_does_not_create_a_storage_value() {
        let mut module = parent(96);
        module.func_types.push(FuncTy {
            abi: None,
            params: vec![Ty::Struct(StructId::new(0))],
            returns: vec![],
            is_vararg: false,
        });
        assert!(matches!(
            admit(&module),
            Err(AdapterError::StorageNotAdmitted {
                violation: trust_ir::StorageViolation {
                    kind: StorageViolationKind::ValueTraffic,
                    ..
                }
            })
        ));
        module.func_types[0].params = vec![Ty::PtrConst(Box::new(Ty::Struct(StructId::new(0))))];
        admit(&module).unwrap();
    }
    #[test]
    fn invalid_geometry_precedes_value_traffic_and_stack_slot_bounds_are_not_widened() {
        let mut module = Module::new("invalid_storage");
        let invalid = Ty::Storage(StorageLayout::new(80, 0));
        module.types.push(invalid.clone());
        module.func_types.push(FuncTy {
            abi: None,
            params: vec![invalid],
            returns: vec![],
            is_vararg: false,
        });
        assert!(matches!(
            admit(&module),
            Err(AdapterError::StorageNotAdmitted {
                violation: trust_ir::StorageViolation {
                    kind: StorageViolationKind::InvalidGeometry(_),
                    ..
                }
            })
        ));
        assert!(
            Geometry {
                size_bytes: 1_u64 << 32,
                align_bytes: 8
            }
            .stack_slot()
            .is_err()
        );
        assert!(
            Geometry {
                size_bytes: 0,
                align_bytes: 1_u64 << 32
            }
            .stack_slot()
            .is_err()
        );
        assert_eq!(
            Geometry {
                size_bytes: 0,
                align_bytes: 32
            }
            .stack_slot()
            .unwrap(),
            (0, 32)
        );
    }
    #[test]
    fn duplicate_nominal_declarations_do_not_gain_first_row_geometry_authority() {
        let mut module = parent(96);
        let mut duplicate = module.structs[0].clone();
        duplicate.size = Some(104);
        module.structs.push(duplicate);
        let error = Resolver::default()
            .resolve(Some(&module), &Ty::Struct(StructId::new(0)))
            .err()
            .expect("ambiguous layout refuses")
            .to_string();
        assert!(error.contains("duplicate struct"), "{error}");
    }
}
