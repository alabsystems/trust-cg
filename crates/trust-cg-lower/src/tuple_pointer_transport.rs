// Copyright 2026 Andrew Yates | Apache-2.0

//! Declared tuples may cross a pointer transport boundary without invoking
//! the legacy tuple layout algorithm. Keep every descriptor in the original
//! module and reject any use that could ask that algorithm for an offset,
//! allocation extent, aggregate value or array stride.

use std::collections::HashSet;
use trust_ir::{CastOp, Inst, Module, Ty, TyId};

fn primitive(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::F32
            | Ty::F64
    )
}

pub(crate) fn admits(module: &Module) -> bool {
    if module.tuple_layouts.len() > 65_536 {
        return false;
    }
    // Check flatness before any recursive layout/structural comparison.
    for descriptor in &module.tuple_layouts {
        let Some(Ty::Tuple(fields)) = module.types.get(descriptor.tuple_type.index() as usize)
        else {
            return false;
        };
        if fields.is_empty() || fields.len() > 65_536 || fields.iter().any(|ty| !primitive(ty)) {
            return false;
        }
    }
    if module.validate_tuple_layouts().is_err() {
        return false;
    }
    let mut expected_tuples = 0;
    for (index, ty) in module.types.iter().enumerate() {
        if let Ty::Tuple(_) = ty {
            if !module
                .tuple_layouts
                .iter()
                .any(|d| d.tuple_type.index() as usize == index)
                || module.ty_layout_shape(ty).is_err()
            {
                return false;
            }
            expected_tuples += 1;
        }
    }
    let mut used: HashSet<TyId> = HashSet::new();
    let mut pointer = |ty: &Ty| {
        if let Ty::Ref(p) | Ty::RefMut(p) | Ty::PtrConst(p) | Ty::PtrMut(p) = ty
            && let Ty::Tuple(_) = p.as_ref()
            && let Ok(Some(descriptor)) = module.tuple_layout_descriptor(p)
        {
            used.insert(descriptor.tuple_type);
            expected_tuples += 1;
        }
    };
    for sig in &module.func_types {
        for ty in sig.params.iter().chain(&sig.returns) {
            pointer(ty);
        }
    }
    for function in &module.functions {
        for block in &function.blocks {
            for (_, ty) in &block.params {
                pointer(ty);
            }
            for node in &block.body {
                if let Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty,
                    dst_ty,
                    ..
                } = &node.inst
                {
                    pointer(src_ty);
                    pointer(dst_ty);
                }
            }
        }
    }
    let mut actual_tuples = 0;
    let mut unsupported = false;
    module.visit_types(|ty| {
        actual_tuples += usize::from(matches!(ty, Ty::Tuple(_)));
        // The inline visitor does not follow table-backed element IDs. A flat
        // primitive array cannot hide a tuple use and its stride is independent
        // of every tuple descriptor. Other table-backed types remain refused.
        let primitive_array = matches!(ty, Ty::Array(element, _)
            if module.types.get(element.index() as usize).is_some_and(primitive));
        unsupported |= !(primitive(ty)
            || primitive_array
            || matches!(
                ty,
                Ty::Tuple(_)
                    | Ty::Ref(_)
                    | Ty::RefMut(_)
                    | Ty::PtrConst(_)
                    | Ty::PtrMut(_)
                    | Ty::Ptr
                    | Ty::Unit
                    | Ty::Never
                    | Ty::Func(_)
            ));
    });
    !unsupported && actual_tuples == expected_tuples && used.len() == module.tuple_layouts.len()
}
