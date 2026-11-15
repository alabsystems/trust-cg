// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Producer-observed closure offsets, with the native carrier's ABI totals.
//!
//! Offsets may be reordered. Size and alignment must match the LIR carrier,
//! because the downstream ABI only retains that carrier, not a closure ID.

use crate::adapter::{AdapterError, translate_type_with_enum_tables};
use crate::declared_layout::{
    EmittedStructLayout, LayoutSource, LayoutTables, emitted_field_layout,
};
use crate::types::Type;
use trust_ir::{ClosureTyId, Module, Ty};

pub(crate) fn admit(module: &Module) -> Result<(), AdapterError> {
    if module.closure_layouts.is_empty() {
        return Ok(());
    }
    module
        .validate_closure_layouts()
        .map_err(|error| AdapterError::TrustIrAdmissionRefused {
            error: error.to_string(),
        })?;
    for descriptor in &module.closure_layouts {
        layout(module, descriptor.closure)?;
    }
    Ok(())
}

pub(crate) fn layout(
    module: &Module,
    id: ClosureTyId,
) -> Result<Option<EmittedStructLayout>, AdapterError> {
    let refuse = |detail: &str| {
        AdapterError::UnsupportedType(format!(
            "[TCG-CLOSURE-LAYOUT] closure.{} declared capture layout {detail}",
            id.index()
        ))
    };
    let mut rows = module
        .closure_layouts
        .iter()
        .filter(|row| row.closure == id);
    let Some(row) = rows.next() else {
        return Ok(None);
    };
    if rows.next().is_some() {
        return Err(refuse("is duplicated"));
    }
    let def = module
        .closure_types
        .get(id.as_usize())
        .ok_or_else(|| refuse("names an absent closure type"))?;
    if row.capture_offsets.len() != def.captures.len() {
        return Err(refuse("does not describe every capture"));
    }
    let carrier = translate_type_with_enum_tables(
        &Ty::Closure(id),
        &module.structs,
        &module.types,
        &module.enums,
        &module.records,
        &module.closure_types,
    )?;
    let Type::Struct(fields) = &carrier else {
        return Err(refuse("has no native struct carrier"));
    };
    if carrier.checked_bytes() != Some(row.size) || u64::from(carrier.align()) != row.align {
        return Err(AdapterError::DeclaredClosureLayoutUnsupported {
            module: module.name.clone(),
            layouts: module.closure_layouts.len(),
        });
    }
    if row.align == 0 || !row.align.is_power_of_two() || row.size % row.align != 0 {
        return Err(refuse("has incoherent size or alignment"));
    }
    // The x86 SysV register classifier also reads the carrier's field order.
    // An observed image may move offsets without moving INTEGER/SSE classes;
    // otherwise the current carrier does not represent that ABI placement.
    if module.target_info.as_ref().is_some_and(|target| {
        target.triple.starts_with("x86_64-") && !target.triple.contains("windows")
    }) && !crate::x86_64_isel::declared_aggregate_preserves_sysv_classes(
        &carrier,
        &row.capture_offsets,
    ) {
        return Err(refuse(
            "changes native register classes not represented by the carrier",
        ));
    }
    let tables = LayoutTables {
        structs: &module.structs,
        types: &module.types,
        enums: &module.enums,
        records: &module.records,
        closures: &module.closure_types,
    };
    let mut images = Vec::with_capacity(fields.len());
    for ((ty, lir), offset) in def.captures.iter().zip(fields).zip(&row.capture_offsets) {
        let field = emitted_field_layout(ty, lir, tables, 0)?;
        if field.align == 0 || field.align > row.align || offset % field.align != 0 {
            return Err(refuse("misaligns a capture's emitted image"));
        }
        let end = offset
            .checked_add(field.size)
            .filter(|end| *end <= row.size)
            .ok_or_else(|| refuse("does not contain a capture's emitted image"))?;
        if field.size != 0 {
            images.push((*offset, end));
        }
    }
    images.sort_unstable();
    if images.windows(2).any(|pair| pair[0].1 > pair[1].0) {
        return Err(refuse("overlaps capture images"));
    }
    Ok(Some(EmittedStructLayout {
        offsets: row.capture_offsets.clone(),
        size: row.size,
        align: row.align,
        source: LayoutSource::Declared,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module() -> Module {
        let mut module = Module::new("observed_closure");
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        let func = module
            .add_func_type(trust_ir::FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
        module.closure_types.push(trust_ir::ClosureTy {
            func,
            captures: vec![Ty::U64, Ty::U8],
        });
        module
            .closure_layouts
            .push(trust_ir::ClosureLayoutDescriptor {
                origin: None,
                closure: ClosureTyId::new(0),
                size: 16,
                align: 8,
                capture_offsets: vec![8, 0],
            });
        module
    }

    #[test]
    fn observed_offsets_are_retained_without_changing_abi_totals() {
        let module = module();
        let before = module.clone();
        admit(&module).unwrap();
        let layout = layout(&module, ClosureTyId::new(0)).unwrap().unwrap();
        assert_eq!(layout.offsets, [8, 0]);
        assert_eq!((layout.size, layout.align), (16, 8));
        assert_eq!(module, before);
    }

    #[test]
    fn reordered_x86_mixed_register_classes_require_a_matching_carrier() {
        let mut module = module();
        module.target_info.as_mut().unwrap().triple = "x86_64-apple-darwin".into();
        // Both declared/natural images total 16/8, but a reordered double and
        // integer would swap XMM and GPR locations in SysV calls and returns.
        module.closure_types[0].captures = vec![Ty::F64, Ty::U64];
        assert!(
            admit(&module)
                .unwrap_err()
                .to_string()
                .contains("register classes")
        );
        module.closure_layouts[0].capture_offsets = vec![0, 8];
        admit(&module).unwrap();
        module.closure_types[0].captures = vec![Ty::U64, Ty::U8];
        module.closure_layouts[0].capture_offsets = vec![8, 0];
        admit(&module).unwrap();
    }

    #[test]
    fn incompatible_abi_totals_are_not_recomputed() {
        let mut module = module();
        module.closure_layouts[0].size = 24;
        module.validate_closure_layouts().unwrap();
        assert!(matches!(
            admit(&module),
            Err(AdapterError::DeclaredClosureLayoutUnsupported { .. })
        ));
    }

    #[test]
    fn malformed_or_ambiguous_descriptors_are_refused() {
        for offsets in [vec![0, 0], vec![1, 0], vec![16, 0], vec![8]] {
            let mut module = module();
            module.closure_layouts[0].capture_offsets = offsets;
            assert!(admit(&module).is_err());
        }
        let mut duplicate = module();
        duplicate
            .closure_layouts
            .push(duplicate.closure_layouts[0].clone());
        assert!(admit(&duplicate).is_err());
        let mut dangling = module();
        dangling.closure_layouts[0].closure = ClosureTyId::new(1);
        assert!(admit(&dangling).is_err());
    }
}
