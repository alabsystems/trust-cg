// Copyright 2026 Andrew Yates | Apache-2.0

//! Install producer-derived pointee layouts only where their origins remain
//! explicit: entry parameters and address extraction from those parameters.
//! Structural tuple equality cannot distinguish two Rust nominal types with
//! different layouts. Conflicting declarations, opaque ABI shells and other
//! tuple-producing operations therefore leave the module unclassified.

use trust_ir::{CastOp, Inst, Module, StructPassingPolicy, TupleLayoutDescriptor, Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PointeeLayout {
    pub(crate) ty: Ty,
    pub(crate) size: u64,
    pub(crate) align: u64,
    pub(crate) offsets: Vec<u64>,
}

/// The caller has checked every argument/return against rustc's direct scalar
/// C FnAbi. This helper checks the IR's use of those declarations, then installs
/// all descriptors together. No proof annotation or instruction is rewritten.
pub(crate) fn install(module: &mut Module, layouts: &[PointeeLayout]) -> bool {
    if module.functions.len() != 1
        || module.func_types.len() != 1
        || module.types.iter().any(|ty| !primitive(ty))
        || !module.tuple_layouts.is_empty()
        || !module.structs.is_empty()
        || !module.globals.is_empty()
        || !module.closure_types.is_empty()
        || module.target_info.is_none()
    {
        return false;
    }
    let function = &module.functions[0];
    if function.calling_conv != trust_ir::CallingConv::C {
        return false;
    }
    let Some(signature) = module.func_types.get(function.ty.index() as usize) else {
        return false;
    };
    let Some(entry) = function.blocks.iter().find(|b| b.id == function.entry) else {
        return false;
    };
    if entry.params.len() != signature.params.len()
        || entry
            .params
            .iter()
            .zip(&signature.params)
            .any(|((_, a), b)| a != b)
    {
        return false;
    }
    let tuple_pointee = |ty: &Ty| match ty {
        Ty::Ref(p) | Ty::RefMut(p) | Ty::PtrConst(p) | Ty::PtrMut(p) => {
            matches!(p.as_ref(), Ty::Tuple(_))
        }
        _ => false,
    };
    let mut expected_tuples = 2 * signature.params.iter().filter(|t| tuple_pointee(t)).count();
    for block in &function.blocks {
        for node in &block.body {
            // Nested rather than a let-chain: this crate is edition 2021,
            // where `&& let` is a parse error. Do not let a clippy
            // `collapsible_if` suggestion re-collapse this.
            // EDITION 2021: this crate is `edition = "2021"`, where clippy's
            // suggested `&& let` chain is a PARSE ERROR. Taking that suggestion
            // once already made this crate unbuildable (4d50932d0, reverted by
            // 39d3cc125). The nesting stays until the crate moves to 2024.
            #[allow(clippy::collapsible_if)]
            if let Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty,
                dst_ty: Ty::Ptr,
                operand,
            } = &node.inst
            {
                if tuple_pointee(src_ty)
                    && entry
                        .params
                        .iter()
                        .any(|(v, ty)| v == operand && ty == src_ty)
                {
                    expected_tuples += 1;
                }
            }
        }
    }
    let mut actual_tuples = 0;
    module.visit_types(|ty| actual_tuples += usize::from(matches!(ty, Ty::Tuple(_))));
    if actual_tuples != expected_tuples {
        return false;
    }

    let mut candidate = Module::new("signature-layouts");
    candidate.target_info = module.target_info.clone();
    candidate.types = module.types.clone();
    let mut distinct: Vec<&PointeeLayout> = Vec::new();
    for ty in &signature.params {
        if !tuple_pointee(ty) {
            continue;
        }
        let (Ty::Ref(pointee) | Ty::RefMut(pointee) | Ty::PtrConst(pointee) | Ty::PtrMut(pointee)) =
            ty
        else {
            return false;
        };
        let pointee = pointee.as_ref();
        let Some(layout) = layouts.iter().find(|l| &l.ty == pointee) else {
            return false;
        };
        if layouts.iter().any(|l| l.ty == layout.ty && l != layout) {
            return false;
        }
        if distinct.iter().any(|l| l.ty == layout.ty) {
            continue;
        }
        // Nested/opaque fields need their own origin transport. This profile
        // carries flat primitive fields, never an inferred lane-tuple layout.
        let Ty::Tuple(fields) = &layout.ty else {
            return false;
        };
        if fields.is_empty() || fields.iter().any(|ty| !primitive(ty)) {
            return false;
        }
        // A full type table installs nothing: fail closed, like every other
        // refusal of this profile.
        let Ok(id) = candidate.add_type(layout.ty.clone()) else {
            return false;
        };
        candidate.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: id,
            size: layout.size,
            align: layout.align,
            field_offsets: layout.offsets.clone(),
        });
        if candidate.ty_layout_shape(&layout.ty).is_err() {
            return false;
        }
        distinct.push(layout);
    }
    // No by-value aggregate crosses this producer-checked C signature. The
    // module already carries `NativeC` (`rustc_signature_layouts::
    // STRUCT_PASSING`, every module since 2026-09-25); restating it here keeps
    // this profile's own contract explicit. It certifies no Rust reference and
    // grants no memory access permission.
    let Some(target_info) = module.target_info.as_mut() else {
        return false;
    };
    target_info.struct_passing = StructPassingPolicy::NativeC;
    module.types = candidate.types;
    module.tuple_layouts = candidate.tuple_layouts;
    true
}

pub(crate) fn primitive(ty: &Ty) -> bool {
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
