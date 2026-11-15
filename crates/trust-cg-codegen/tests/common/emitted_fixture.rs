// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Frozen frontend-emitted trust-ir fixtures, brought to the module a
//! conforming producer emits before they are compiled.
//!
//! The embedded modules are byte-identical artifacts of earlier trust-ir
//! frontend (`trust_ir_mir`) runs, kept verbatim so they can be regenerated and
//! diffed. Those emitters had two producer defects trust-ir's validator now
//! refuses, and since WS7.3 every trust-cg ingestion entry refuses what the
//! validator refuses:
//!
//! * no `target_info` beside a bodyless declaration (`TargetInfoRequired`:
//!   an FFI boundary needs a pinned target) — the target the fixture is
//!   compiled for is pinned (the host for a JIT fixture);
//! * one bodyless declaration per call site of the same symbol and signature
//!   (`DuplicateFunctionSymbol`: `Function.name` is the link-time symbol) —
//!   the module-batching merge folds declarations by symbol, so every call
//!   through any copy reaches the one entry;
//! * a shift whose amount has another integer type than the shifted value
//!   (MIR's `u32 << i32`; `BinOpTypeMismatch`: a trust-ir `BinOp` has ONE
//!   operand type) — the amount is converted to the value's type first:
//!   `Bitcast` at the same width, `ZExt` from a narrower one, `Trunc` from a
//!   wider one. An in-range amount (the only one with defined behaviour) is
//!   the same number after each.
//!
//! Nothing else is changed: a fixture with any other finding is refused by
//! name, as it should be.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, CastOp, Endianness, Inst, InstrNode, Module, StructPassingPolicy, TargetInfo, Ty,
    ValueId,
};

/// The host triple the fixtures are JIT-compiled for.
fn host_triple() -> &'static str {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("aarch64", "macos") => "aarch64-apple-darwin",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("aarch64", _) => "aarch64-unknown-linux-gnu",
        _ => "x86_64-unknown-linux-gnu",
    }
}

/// `module` with the producer defects above repaired, pinned to the host.
pub fn conform(module: Module) -> Module {
    conform_for(module, host_triple())
}

/// [`conform`], pinning `triple` (a 64-bit little-endian target) when the
/// module names none.
pub fn conform_for(mut module: Module, triple: &str) -> Module {
    if module.target_info.is_none() {
        module.target_info = Some(TargetInfo {
            triple: triple.into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
    }
    for index in 0..module.functions.len() {
        let rewritten = widen_shift_amounts(&module, index);
        if let Some(blocks) = rewritten {
            module.functions[index].blocks = blocks;
        }
    }
    let mut names = HashSet::new();
    let duplicate_symbol = module
        .functions
        .iter()
        .any(|function| !names.insert(function.name.as_str()));
    if duplicate_symbol {
        // A merge refusal leaves the module as emitted: its compile then names
        // the defect.
        if let Ok(folded) =
            trust_cg_codegen::module_merge::merge_modules(std::slice::from_ref(&module))
        {
            return folded;
        }
    }
    module
}

/// Parse an embedded emitted fixture and [`conform`] it.
pub fn parse_emitted(text: &str) -> Result<Module, trust_ir::parser::ParseError> {
    trust_ir::parser::parse_module(text).map(conform)
}

/// Parse an embedded emitted fixture and [`conform_for`] it to `triple`.
pub fn parse_emitted_for(text: &str, triple: &str) -> Result<Module, trust_ir::parser::ParseError> {
    trust_ir::parser::parse_module(text).map(|module| conform_for(module, triple))
}

/// The type of every value of function `index` that the shift repair needs
/// (block parameters and the results of the instructions whose result type
/// the instruction states); a value of any other origin is absent.
fn value_types(module: &Module, index: usize) -> HashMap<u32, Ty> {
    let function = &module.functions[index];
    let mut types = HashMap::new();
    for block in &function.blocks {
        for (value, ty) in &block.params {
            types.insert(value.index(), ty.clone());
        }
        for node in &block.body {
            let stated = match &node.inst {
                Inst::Const { ty, .. }
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::Load { ty, .. }
                | Inst::Copy { ty, .. }
                | Inst::Select { ty, .. } => Some(ty.clone()),
                Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
                Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => Some(ty.comparison_result_ty()),
                Inst::Call { callee, .. } => {
                    for (position, result) in node.results.iter().enumerate() {
                        let returned = module
                            .functions
                            .iter()
                            .find(|candidate| candidate.id == *callee)
                            .and_then(|callee| module.func_types.get(callee.ty.index() as usize))
                            .and_then(|signature| signature.returns.get(position));
                        if let Some(ty) = returned {
                            types.insert(result.index(), ty.clone());
                        }
                    }
                    None
                }
                _ => None,
            };
            if let (Some(ty), [result]) = (stated, node.results.as_slice()) {
                types.insert(result.index(), ty);
            }
        }
    }
    types
}

/// Function `index`'s blocks with every mixed-type shift amount converted
/// (see the module docs), or `None` when it has none.
fn widen_shift_amounts(module: &Module, index: usize) -> Option<Vec<trust_ir::Block>> {
    let function = &module.functions[index];
    let types = value_types(module, index);
    let mut next = function
        .blocks
        .iter()
        .flat_map(|block| {
            block.params.iter().map(|(value, _)| value.index()).chain(
                block
                    .body
                    .iter()
                    .flat_map(|node| node.results.iter().map(|v| v.index())),
            )
        })
        .max()
        .map_or(0, |max| max + 1);
    let mut changed = false;
    let mut blocks = function.blocks.clone();
    for block in &mut blocks {
        let mut body = Vec::with_capacity(block.body.len());
        for mut node in std::mem::take(&mut block.body) {
            if let Inst::BinOp {
                op: BinOp::Shl | BinOp::LShr | BinOp::AShr,
                ty,
                rhs,
                ..
            } = &mut node.inst
                && let Some(amount_ty) = types.get(&rhs.index())
                && amount_ty != ty
                && amount_ty.is_integer()
                && ty.is_integer()
                && let (Some(from), Some(to)) = (amount_ty.bit_width(), ty.bit_width())
            {
                let op = match from.cmp(&to) {
                    std::cmp::Ordering::Equal => CastOp::Bitcast,
                    std::cmp::Ordering::Less => CastOp::ZExt,
                    std::cmp::Ordering::Greater => CastOp::Trunc,
                };
                let converted = ValueId::new(next);
                next += 1;
                body.push(
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty: amount_ty.clone(),
                        dst_ty: ty.clone(),
                        operand: *rhs,
                    })
                    .with_result(converted),
                );
                *rhs = converted;
                changed = true;
            }
            body.push(node);
        }
        block.body = body;
    }
    changed.then_some(blocks)
}
