// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Rewrite a fixture's aggregate-typed `ExtractField` into trust-ir's spelling.
//!
//! Many hand-built fixtures spell `ExtractField.ty` as the AGGREGATE's type, a
//! legacy convention trust-cg's adapter reads (`field_extract_types` accepts
//! either). trust-ir's `ExtractField.ty` is the extracted FIELD's type — the
//! result — and its validator refuses the aggregate spelling
//! (`OperandTypeMismatch` on the extract and on every use of its result).
//! Since WS7.3 every trust-cg ingestion entry refuses what the validator
//! refuses, so [`normalize`] rewrites exactly the extracts whose `ty` IS their
//! aggregate operand's type to that aggregate's declared field type. An
//! extract whose aggregate type this pass cannot see is left alone (and is
//! then refused by name if it is wrong).

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::collections::HashMap;

use trust_ir::{Inst, Module, Ty};

/// The declared type of field `field` of aggregate type `ty`, when `ty` is a
/// struct or tuple of `module`.
fn field_ty(module: &Module, ty: &Ty, field: u32) -> Option<Ty> {
    match ty {
        Ty::Struct(id) => module
            .structs
            .iter()
            .find(|def| def.id == *id)
            .and_then(|def| def.fields.get(field as usize))
            .map(|field| field.ty.clone()),
        Ty::Tuple(lanes) => lanes.get(field as usize).cloned(),
        _ => None,
    }
}

/// See the module docs. One pass per function in block order; an extract's
/// (corrected) result type is known to the extracts that read it, so nested
/// aggregates are rewritten too.
pub fn normalize(module: &mut Module) {
    let table = module.clone();
    for function in &mut module.functions {
        let mut types: HashMap<u32, Ty> = HashMap::new();
        for block in &function.blocks {
            for (value, ty) in &block.params {
                types.insert(value.index(), ty.clone());
            }
        }
        for block in &mut function.blocks {
            for node in &mut block.body {
                let stated = match &mut node.inst {
                    Inst::ExtractField {
                        ty,
                        aggregate,
                        field,
                    } => {
                        if types.get(&aggregate.index()) == Some(&*ty)
                            && let Some(declared) = field_ty(&table, ty, *field)
                        {
                            *ty = declared;
                        }
                        Some(ty.clone())
                    }
                    Inst::Const { ty, .. }
                    | Inst::Load { ty, .. }
                    | Inst::Copy { ty, .. }
                    | Inst::InsertField { ty, .. } => Some(ty.clone()),
                    Inst::Call { callee, .. } => table
                        .functions
                        .iter()
                        .find(|candidate| candidate.id == *callee)
                        .and_then(|callee| table.func_types.get(callee.ty.index() as usize))
                        .and_then(|signature| signature.returns.first().cloned()),
                    Inst::CallIndirect { sig, .. } => table
                        .func_types
                        .get(sig.index() as usize)
                        .and_then(|signature| signature.returns.first().cloned()),
                    _ => None,
                };
                if let (Some(ty), [result]) = (stated, node.results.as_slice()) {
                    types.insert(result.index(), ty);
                }
            }
        }
    }
}

/// A copy of `module` with [`normalize`] applied.
pub fn normalized(module: &Module) -> Module {
    let mut module = module.clone();
    normalize(&mut module);
    module
}
