// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Typed nominal values without a machine register, address or Unit surrogate.
//! Actual source nodes and their catalog/SSA/use relations remain held. This
//! semantic transport grants no body licence, source NoUB or proof authority.

use std::collections::BTreeMap;

use crate::{AdapterError, NativeAbiContext};
use trust_ir::analysis::{DominatorTree, SsaDefinitionSite, SsaUseSite};
use trust_ir::{
    BlockId, CastOp, Constant, FuncId, FuncTyId, Function, Inst, InstrNode, Module,
    ModuleFunctionCatalog, Ty, ValueId,
};

#[path = "native_nominal_values/private_memory.rs"]
mod private_memory;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Action {
    Value { target: FuncId },
    Reify { target: FuncId, signature: FuncTyId },
    Call { target: FuncId },
    PrivateMemory,
}

struct Definition<'a> {
    site: SsaDefinitionSite,
    ty: Ty,
    node: Option<&'a InstrNode>,
}

struct NodeAction<'a> {
    node: &'a InstrNode,
    action: Action,
}

struct Values<'a> {
    function: &'a Function,
    values: BTreeMap<ValueId, FuncId>,
    private_pointers: std::collections::BTreeSet<ValueId>,
    actions: BTreeMap<(BlockId, usize), NodeAction<'a>>,
}

pub(crate) struct ModuleValues<'a> {
    module: &'a Module,
    functions: BTreeMap<FuncId, Values<'a>>,
}

impl<'a> ModuleValues<'a> {
    pub(crate) fn native(
        module: &'a Module,
        native: &NativeAbiContext,
    ) -> Result<Self, AdapterError> {
        let affected: Vec<_> = module
            .functions
            .iter()
            .filter(|function| mentions_nominal(function, module))
            .collect();
        if affected.is_empty() {
            return Ok(Self {
                module,
                functions: BTreeMap::new(),
            });
        }
        native.admit_module(module)?;
        let catalog = ModuleFunctionCatalog::new(module);
        let mut functions = BTreeMap::new();
        for function in affected {
            let (actual, signature) = catalog.function_item(function.id).map_err(refusal)?;
            if !std::ptr::eq(actual, function) {
                return Err(refusal(
                    "nominal source function is not its actual catalog object",
                ));
            }
            // The selected target/profile must already implement every real
            // function boundary. A nominal value is no ABI opt-out.
            native.source_prototype(module, signature, function.calling_conv)?;
            let values = analyze(function, module, &catalog)?;
            if functions.insert(function.id, values).is_some() {
                return Err(refusal("nominal source repeats a function identity"));
            }
        }
        Ok(Self { module, functions })
    }

    pub(crate) fn check_function(
        &self,
        module: &Module,
        function: &Function,
    ) -> Result<(), AdapterError> {
        if !std::ptr::eq(self.module, module) {
            return Err(refusal("nominal values belong to another module object"));
        }
        if let Some(values) = self.functions.get(&function.id)
            && !std::ptr::eq(values.function, function)
        {
            return Err(refusal("nominal values belong to another function object"));
        }
        Ok(())
    }

    pub(crate) fn action(
        &self,
        function: &Function,
        block: BlockId,
        instruction: usize,
        node: &InstrNode,
    ) -> Result<Option<Action>, AdapterError> {
        self.check_function(self.module, function)?;
        let Some(values) = self.functions.get(&function.id) else {
            return Ok(None);
        };
        let Some(action) = values.actions.get(&(block, instruction)) else {
            return Ok(None);
        };
        if !std::ptr::eq(action.node, node) {
            return Err(refusal(
                "nominal operation is detached from its actual source node",
            ));
        }
        Ok(Some(action.action))
    }

    #[cfg(test)]
    pub(crate) fn target(&self, function: FuncId, value: ValueId) -> Option<FuncId> {
        self.functions.get(&function)?.values.get(&value).copied()
    }

    pub(crate) fn is_semantic_value(&self, function: FuncId, value: ValueId) -> bool {
        self.functions.get(&function).is_some_and(|values| {
            values.values.contains_key(&value) || values.private_pointers.contains(&value)
        })
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

fn mentions_nominal(function: &Function, module: &Module) -> bool {
    function.blocks.iter().any(|block| {
        block
            .params
            .iter()
            .any(|(_, ty)| matches!(ty, Ty::FnItem(_)))
            || block.body.iter().any(|node| {
                let mut found = false;
                // BoxDeref computes only its pointer. The independently
                // checked/reported pointee fact is not a nominal SSA value
                // and must not require this unrelated singleton protocol.
                if !matches!(node.inst, Inst::BoxDeref { .. }) {
                    node.inst
                        .visit_type_roots(|ty| found |= matches!(ty, Ty::FnItem(_)));
                }
                found
                    || node
                        .result_tys(module)
                        .iter()
                        .any(|ty| matches!(ty, Ty::FnItem(_)))
                    || matches!(&node.inst, Inst::Const { value, .. } if carries_item(value))
            })
    })
}

fn carries_item(value: &Constant) -> bool {
    value
        .try_visit_constants(|value| {
            if matches!(value, Constant::FnItem(_)) {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
}

fn analyze<'a>(
    function: &'a Function,
    module: &'a Module,
    catalog: &ModuleFunctionCatalog<'a>,
) -> Result<Values<'a>, AdapterError> {
    let mut definitions = BTreeMap::new();
    let mut blocks = std::collections::BTreeSet::new();
    for block in &function.blocks {
        if !blocks.insert(block.id) {
            return Err(refusal("nominal SSA repeats a block identity"));
        }
        for (value, ty) in &block.params {
            let definition = Definition {
                site: SsaDefinitionSite {
                    block: block.id,
                    instruction: None,
                },
                ty: ty.clone(),
                node: None,
            };
            if definitions.insert(*value, definition).is_some() {
                return Err(refusal("nominal SSA repeats a definition"));
            }
        }
        for (instruction, node) in block.body.iter().enumerate() {
            let types = node.result_tys(module);
            if types.len() != node.results.len() {
                return Err(refusal("nominal SSA result census is incomplete"));
            }
            for (value, ty) in node.results.iter().zip(types) {
                let definition = Definition {
                    site: SsaDefinitionSite {
                        block: block.id,
                        instruction: Some(instruction),
                    },
                    ty,
                    node: Some(node),
                };
                if definitions.insert(*value, definition).is_some() {
                    return Err(refusal("nominal SSA repeats a definition"));
                }
            }
        }
    }
    let mut values = BTreeMap::new();
    for (value, definition) in &definitions {
        let Ty::FnItem(target) = definition.ty else {
            continue;
        };
        catalog.function_item(target).map_err(refusal)?;
        let node = definition.node.ok_or_else(|| {
            refusal("nominal formal/block parameter needs its actual physical ABI projection")
        })?;
        if node.results.as_slice() != [*value] || !node.proofs.is_empty() {
            return Err(refusal(
                "nominal result/proof needs a complete typed non-runtime transport",
            ));
        }
        match &node.inst {
            Inst::Const {
                ty: Ty::FnItem(expected),
                value: Constant::FnItem(actual),
            } if *expected == target && actual == expected => {}
            Inst::Copy {
                ty: Ty::FnItem(expected),
                ..
            } if *expected == target => {}
            // The closed private-object analysis below must independently
            // prove exact provenance, initialization and every pointer use.
            Inst::Load {
                ty: Ty::FnItem(expected),
                ..
            } if *expected == target => {}
            // Undef, unknown memory and aggregate projections are not valid
            // constants merely because their nominal type has size0.
            _ => {
                return Err(refusal(
                    "nominal value producer/poison/memory contract is not implemented",
                ));
            }
        }
        values.insert(*value, target);
    }
    let dominators = DominatorTree::new(function);
    if !dominators.is_well_formed() {
        return Err(refusal("nominal SSA has an unusable CFG"));
    }
    let private_memory =
        private_memory::analyze(function, catalog, &definitions, &values, &dominators)?;
    let mut actions = BTreeMap::new();
    for block in &function.blocks {
        for (instruction, node) in block.body.iter().enumerate() {
            let mut operands = Vec::new();
            node.inst.visit_value_operands(|value| {
                if let Some(target) = values.get(&value) {
                    operands.push((value, *target));
                }
            });
            for (value, _) in &operands {
                let definition = definitions
                    .get(value)
                    .ok_or_else(|| refusal("missing nominal definition"))?;
                if !dominators.definition_available_at(
                    definition.site,
                    SsaUseSite::BeforeInstruction {
                        block: block.id,
                        instruction,
                    },
                ) {
                    return Err(refusal(
                        "nominal definition does not dominate this actual use",
                    ));
                }
            }
            let action = match &node.inst {
                Inst::Const {
                    ty: Ty::FnItem(target),
                    value: Constant::FnItem(actual),
                } if target == actual && node.results.len() == 1 => {
                    Some(Action::Value { target: *target })
                }
                Inst::Copy {
                    ty: Ty::FnItem(target),
                    operand,
                } if node.results.len() == 1 && values.get(operand) == Some(target) => {
                    Some(Action::Value { target: *target })
                }
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::FnItem(target),
                    dst_ty: Ty::Func(signature),
                    operand,
                } if node.results.len() == 1 && values.get(operand) == Some(target) => {
                    let (callee, target_signature) =
                        catalog.function_item(*target).map_err(refusal)?;
                    if callee.ty != *signature || target_signature.abi.is_none() {
                        return Err(refusal(
                            "nominal reification changed the exact target signature",
                        ));
                    }
                    Some(Action::Reify {
                        target: *target,
                        signature: *signature,
                    })
                }
                Inst::CallIndirect {
                    callee,
                    sig,
                    calling_conv,
                    args,
                } if values.contains_key(callee) => {
                    let target = values[callee];
                    let (target_function, target_signature) =
                        catalog.function_item(target).map_err(refusal)?;
                    if target_function.ty != *sig
                        || target_function.calling_conv != *calling_conv
                        || target_signature.abi.is_none()
                        || args.len() != target_signature.params.len()
                        || args
                            .iter()
                            .zip(&target_signature.params)
                            .any(|(value, ty)| {
                                definitions
                                    .get(value)
                                    .is_none_or(|definition| definition.ty != *ty)
                            })
                    {
                        return Err(refusal(
                            "nominal call changed the actual target signature/convention",
                        ));
                    }
                    Some(Action::Call { target })
                }
                _ => None,
            }
            .or_else(|| {
                private_memory
                    .actions
                    .get(&(block.id, instruction))
                    .map(|action| action.action)
            });
            let mut nominal_type = false;
            node.inst
                .visit_type_roots(|ty| nominal_type |= matches!(ty, Ty::FnItem(_)));
            if action.is_none()
                && (!operands.is_empty()
                    || nominal_type
                    || matches!(&node.inst, Inst::Const { value, .. } if carries_item(value)))
            {
                return Err(refusal(
                    "nominal use/aggregate/zero-byte memory semantics is not implemented",
                ));
            }
            if let Some(action) = action {
                actions.insert((block.id, instruction), NodeAction { node, action });
            }
        }
    }
    Ok(Values {
        function,
        values,
        private_pointers: private_memory.pointers,
        actions,
    })
}

fn refusal(reason: impl std::fmt::Display) -> AdapterError {
    AdapterError::UnsupportedInstruction(format!("[TCG-NOMINAL-VALUE] {reason}"))
}

#[cfg(test)]
#[path = "native_nominal_values_tests.rs"]
mod tests;
