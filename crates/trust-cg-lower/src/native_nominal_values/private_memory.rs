// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Closed private nominal slots. These are semantic objects with exact source
//! provenance, not null pointers or zero-byte machine allocations. Every use is
//! checked before the object can be promoted away.

use super::*;
use std::collections::BTreeSet;

pub(super) struct Memory<'a> {
    pub(super) pointers: BTreeSet<ValueId>,
    pub(super) actions: BTreeMap<(BlockId, usize), NodeAction<'a>>,
}

struct Object {
    target: FuncId,
    block: BlockId,
    initialized: bool,
}

pub(super) fn analyze<'a>(
    function: &'a Function,
    catalog: &ModuleFunctionCatalog<'a>,
    definitions: &BTreeMap<ValueId, Definition<'a>>,
    values: &BTreeMap<ValueId, FuncId>,
    dominators: &DominatorTree,
) -> Result<Memory<'a>, AdapterError> {
    let mut objects = BTreeMap::new();
    let mut actions = BTreeMap::new();
    for block in &function.blocks {
        for (instruction, node) in block.body.iter().enumerate() {
            if let Inst::Alloca {
                ty: Ty::FnItem(target),
                count,
                align,
            } = &node.inst
            {
                catalog.function_item(*target).map_err(refusal)?;
                let [pointer] = node.results.as_slice() else {
                    return Err(refusal(
                        "private nominal object needs one actual pointer definition",
                    ));
                };
                if count.is_some()
                    || !matches!(align, None | Some(1))
                    || !node.proofs.is_empty()
                    || definitions
                        .get(pointer)
                        .is_none_or(|definition| definition.ty != Ty::Ptr)
                {
                    return Err(refusal(
                        "private nominal object needs a single alignment-one slot without proof metadata",
                    ));
                }
                objects.insert(
                    *pointer,
                    Object {
                        target: *target,
                        block: block.id,
                        initialized: false,
                    },
                );
                actions.insert(
                    (block.id, instruction),
                    NodeAction {
                        node,
                        action: Action::PrivateMemory,
                    },
                );
            }
        }
    }
    for block in &function.blocks {
        for (instruction, node) in block.body.iter().enumerate() {
            let mut pointers = BTreeSet::new();
            node.inst.visit_value_operands(|value| {
                if objects.contains_key(&value) {
                    pointers.insert(value);
                }
            });
            for pointer in pointers {
                let object = objects.get_mut(&pointer).unwrap();
                let definition = definitions
                    .get(&pointer)
                    .ok_or_else(|| refusal("private nominal pointer has no actual definition"))?;
                if object.block != block.id
                    || !dominators.definition_available_at(
                        definition.site,
                        SsaUseSite::BeforeInstruction {
                            block: block.id,
                            instruction,
                        },
                    )
                    || !node.proofs.is_empty()
                {
                    return Err(refusal(
                        "private nominal object crosses its checked lifetime/block or proof boundary",
                    ));
                }
                let action = match &node.inst {
                    Inst::Store {
                        ty: Ty::FnItem(target),
                        ptr,
                        value,
                        volatile: false,
                        align,
                    } if *ptr == pointer
                        && *target == object.target
                        && matches!(align, None | Some(1))
                        && node.results.is_empty()
                        && values.get(value) == Some(target) =>
                    {
                        object.initialized = true;
                        Action::PrivateMemory
                    }
                    Inst::Load {
                        ty: Ty::FnItem(target),
                        ptr,
                        volatile: false,
                        align,
                    } if *ptr == pointer
                        && *target == object.target
                        && matches!(align, None | Some(1))
                        && node.results.len() == 1
                        && object.initialized =>
                    {
                        Action::Value { target: *target }
                    }
                    _ => {
                        return Err(refusal(
                            "private nominal pointer escapes or has an uninitialized, volatile, misaligned or mismatched access",
                        ));
                    }
                };
                actions.insert((block.id, instruction), NodeAction { node, action });
            }
            if matches!(
                node.inst,
                Inst::Load {
                    ty: Ty::FnItem(_),
                    ..
                }
            ) && !actions.contains_key(&(block.id, instruction))
            {
                return Err(refusal(
                    "nominal load lacks its actual closed initialized private object",
                ));
            }
        }
    }
    Ok(Memory {
        pointers: objects.keys().copied().collect(),
        actions,
    })
}
