// trust-cg-dialect - DialectModule / DialectFunction / DialectBlock
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Top-level module containers: [`DialectModule`], [`DialectFunction`], and
//! [`DialectBlock`]. Storage is flat `Vec<DialectOp>` + typed indices, matching
//! the arena style used by `MachFunction` in `trust-cg-ir`.

use trust_cg_ir::Type;

use crate::id::{BlockId, DialectOpId, OpId, ValueId};
use crate::op::{Attributes, DialectOp, SourceRange};
use crate::registry::DialectRegistry;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DialectIdentityDomain {
    Value,
    Block,
    Op,
}

/// Invalid builder requests are rejected before changing the function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DialectBuildError {
    IdentityExhausted(DialectIdentityDomain),
    MissingBlock(BlockId),
    DuplicateBlock(BlockId),
}

impl std::fmt::Display for DialectBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdentityExhausted(domain) => {
                write!(f, "dialect {domain:?} identity namespace exhausted")
            }
            Self::MissingBlock(block) => write!(f, "dialect block {block:?} is absent"),
            Self::DuplicateBlock(block) => write!(f, "dialect block {block:?} is duplicated"),
        }
    }
}

impl std::error::Error for DialectBuildError {}

/// A basic block referencing ops by arena index.
///
/// Blocks may carry SSA parameters — the dialect-level analogue of MLIR basic
/// block arguments / classical SSA phi nodes. The entry block of a function
/// has an empty `params` slice because the function-level parameters serve
/// that role (see [`DialectFunction::new`]); subsequent blocks may declare
/// their own parameter list via [`DialectFunction::new_block_with_params`].
#[derive(Debug, Clone)]
pub struct DialectBlock {
    pub id: BlockId,
    pub ops: Vec<OpId>,
    /// SSA parameters attached to this block. Each entry is
    /// `(value_id, type)` and the value IDs are unique inside the owning
    /// [`DialectFunction`].
    pub params: Vec<(ValueId, Type)>,
}

impl DialectBlock {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            ops: Vec::new(),
            params: Vec::new(),
        }
    }
}

/// A single function in a [`DialectModule`].
#[derive(Debug, Clone)]
pub struct DialectFunction {
    pub name: String,
    pub params: Vec<(ValueId, Type)>,
    pub results: Vec<Type>,
    pub blocks: Vec<DialectBlock>,
    /// Flat op arena. `OpId(i)` indexes `ops[i]`.
    pub ops: Vec<DialectOp>,
    // u32::MAX + 1 explicitly represents exhaustion without losing the final ID.
    next_value: u64,
    next_block: u64,
}

impl DialectFunction {
    /// Construct an empty function and a single entry block.
    ///
    /// Parameter SSA values are allocated in order, so callers receive the
    /// `ValueId`s they need to reference in the body.
    pub fn new(
        name: impl Into<String>,
        params: Vec<Type>,
        results: Vec<Type>,
    ) -> Result<Self, DialectBuildError> {
        let mut f = Self {
            name: name.into(),
            params: Vec::new(),
            results,
            blocks: vec![DialectBlock::new(BlockId(0))],
            ops: Vec::new(),
            next_value: 0,
            next_block: 1,
        };
        let range = f.value_range(params.len())?;
        f.next_value = range.end;
        // value_range validated every identity before narrowing or mutating.
        f.params = range
            .zip(params)
            .map(|(id, ty)| (ValueId(id as u32), ty))
            .collect();
        Ok(f)
    }

    fn value_range(&self, count: usize) -> Result<std::ops::Range<u64>, DialectBuildError> {
        let error = DialectBuildError::IdentityExhausted(DialectIdentityDomain::Value);
        let count = u64::try_from(count).map_err(|_| error)?;
        let end = self
            .next_value
            .checked_add(count)
            .filter(|end| *end <= u64::from(u32::MAX) + 1)
            .ok_or(error)?;
        Ok(self.next_value..end)
    }

    /// Allocate a fresh SSA `ValueId`.
    pub fn alloc_value(&mut self) -> Result<ValueId, DialectBuildError> {
        let range = self.value_range(1)?;
        self.next_value = range.end;
        Ok(ValueId(range.start as u32))
    }

    /// Append a fresh empty block and return its id.
    pub fn new_block(&mut self) -> Result<BlockId, DialectBuildError> {
        let id = self.next_block_id()?;
        self.next_block += 1;
        self.blocks.push(DialectBlock::new(id));
        Ok(id)
    }

    fn next_block_id(&self) -> Result<BlockId, DialectBuildError> {
        let id = BlockId(
            u32::try_from(self.next_block)
                .map_err(|_| DialectBuildError::IdentityExhausted(DialectIdentityDomain::Block))?,
        );
        if self.blocks.iter().any(|block| block.id == id) {
            return Err(DialectBuildError::DuplicateBlock(id));
        }
        Ok(id)
    }

    /// Append a fresh block that carries `param_types` SSA parameters.
    ///
    /// Returns the new block's id along with the freshly-allocated parameter
    /// `ValueId`s in positional order. The block is empty until ops are
    /// appended via [`DialectFunction::append_op`].
    pub fn new_block_with_params(
        &mut self,
        param_types: Vec<Type>,
    ) -> Result<(BlockId, Vec<ValueId>), DialectBuildError> {
        let id = self.next_block_id()?;
        let range = self.value_range(param_types.len())?;
        let end = range.end;
        let params: Vec<_> = range
            .zip(param_types)
            .map(|(id, ty)| (ValueId(id as u32), ty))
            .collect();
        let values = params.iter().map(|(id, _)| *id).collect();
        self.blocks.push(DialectBlock {
            id,
            ops: Vec::new(),
            params,
        });
        self.next_block += 1;
        self.next_value = end;
        Ok((id, values))
    }

    /// Append an op to the given block and return its [`OpId`].
    pub fn append_op(
        &mut self,
        block: BlockId,
        op: DialectOpId,
        results: Vec<(ValueId, Type)>,
        operands: Vec<ValueId>,
        attrs: Attributes,
        source: Option<SourceRange>,
    ) -> Result<OpId, DialectBuildError> {
        let mut matching = self
            .blocks
            .iter_mut()
            .filter(|candidate| candidate.id == block);
        let target = matching
            .next()
            .ok_or(DialectBuildError::MissingBlock(block))?;
        if matching.next().is_some() {
            return Err(DialectBuildError::DuplicateBlock(block));
        }
        let id = OpId(
            u32::try_from(self.ops.len())
                .map_err(|_| DialectBuildError::IdentityExhausted(DialectIdentityDomain::Op))?,
        );
        self.ops.push(DialectOp {
            id,
            op,
            results,
            operands,
            attrs,
            source,
        });
        target.ops.push(id);
        Ok(id)
    }

    /// Check layout, unique definitions and reference existence before indexed
    /// traversal or renumbering. Unplaced arena ops are permitted and ignored.
    /// This does not check SSA dominance, opcode types or terminator semantics.
    pub(crate) fn validate_structure(&self) -> Result<(), String> {
        use std::collections::BTreeSet;

        let invalid = |message: String| format!("{}: {message}", self.name);
        if self.blocks.is_empty() {
            return Err(invalid("source has no entry block".into()));
        }
        let mut blocks = BTreeSet::new();
        for block in &self.blocks {
            if !blocks.insert(block.id) {
                return Err(invalid(format!("duplicate block {:?}", block.id)));
            }
        }
        let mut values = BTreeSet::new();
        for (value, _) in self
            .params
            .iter()
            .chain(self.blocks.iter().flat_map(|block| &block.params))
        {
            if !values.insert(*value) {
                return Err(invalid(format!("duplicate SSA definition {value:?}")));
            }
        }
        let mut placed_ops = BTreeSet::new();
        for block in &self.blocks {
            for id in &block.ops {
                let op = self.ops.get(id.0 as usize).ok_or_else(|| {
                    invalid(format!("block {:?} references missing op {id:?}", block.id))
                })?;
                if op.id != *id {
                    return Err(invalid(format!(
                        "op {id:?} has inconsistent arena identity {:?}",
                        op.id
                    )));
                }
                if !placed_ops.insert(*id) {
                    return Err(invalid(format!("op {id:?} is placed more than once")));
                }
                for (value, _) in &op.results {
                    if !values.insert(*value) {
                        return Err(invalid(format!("duplicate SSA definition {value:?}")));
                    }
                }
                for target in op.block_refs() {
                    if !blocks.contains(&target) {
                        return Err(invalid(format!(
                            "op {id:?} references missing block {target:?}"
                        )));
                    }
                }
            }
        }
        // The first traversal checked every placed arena reference, so iter_ops
        // is safe here. Global definition existence is distinct from dominance.
        for op in self.iter_ops() {
            for value in &op.operands {
                if !values.contains(value) {
                    return Err(invalid(format!(
                        "op {:?} references undefined SSA value {value:?}",
                        op.id
                    )));
                }
            }
        }
        Ok(())
    }

    /// Iterate over ops in program order (block by block).
    /// Callers accepting externally mutated fields must validate layout first.
    pub fn iter_ops(&self) -> impl Iterator<Item = &DialectOp> {
        self.blocks
            .iter()
            .flat_map(move |b| b.ops.iter().map(move |id| &self.ops[id.0 as usize]))
    }

    /// Total op count across all blocks.
    pub fn op_count(&self) -> usize {
        self.blocks.iter().map(|b| b.ops.len()).sum()
    }

    pub fn entry_block(&self) -> Option<BlockId> {
        self.blocks.first().map(|b| b.id)
    }
}

/// A container of [`DialectFunction`]s plus the [`DialectRegistry`] describing
/// the dialects they reference.
pub struct DialectModule {
    pub name: String,
    pub functions: Vec<DialectFunction>,
    pub registry: DialectRegistry,
}

impl DialectModule {
    pub fn new(name: impl Into<String>, registry: DialectRegistry) -> Self {
        Self {
            name: name.into(),
            functions: Vec::new(),
            registry,
        }
    }

    pub fn push_function(&mut self, f: DialectFunction) -> usize {
        self.functions.push(f);
        self.functions.len() - 1
    }

    /// Resolve an op to its static op-definition via the registry.
    pub fn resolve(&self, op: DialectOpId) -> Option<&crate::dialect::OpDef> {
        self.registry.op_def(op)
    }
}

impl std::fmt::Debug for DialectModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DialectModule")
            .field("name", &self.name)
            .field("functions", &self.functions.len())
            .field("registry", &self.registry)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{DialectId, OpCode};

    fn function() -> DialectFunction {
        DialectFunction::new("boundary", Vec::new(), Vec::new()).unwrap()
    }

    fn append(function: &mut DialectFunction, block: BlockId) -> Result<OpId, DialectBuildError> {
        function.append_op(
            block,
            DialectOpId::new(DialectId(0), OpCode(0)),
            Vec::new(),
            Vec::new(),
            Attributes::default(),
            None,
        )
    }

    #[test]
    fn value_allocator_preserves_the_final_id_and_reports_exhaustion() {
        let mut function = function();
        function.next_value = u64::from(u32::MAX);
        assert_eq!(function.alloc_value(), Ok(ValueId(u32::MAX)));
        assert_eq!(
            function.alloc_value(),
            Err(DialectBuildError::IdentityExhausted(
                DialectIdentityDomain::Value
            ))
        );
        assert_eq!(function.next_value, u64::from(u32::MAX) + 1);
    }

    #[test]
    fn block_allocator_preserves_the_final_id_and_reports_exhaustion() {
        let mut function = function();
        function.next_block = u64::from(u32::MAX);
        assert_eq!(function.new_block(), Ok(BlockId(u32::MAX)));
        assert_eq!(
            function.new_block(),
            Err(DialectBuildError::IdentityExhausted(
                DialectIdentityDomain::Block
            ))
        );
        assert_eq!(function.blocks.len(), 2);
    }

    #[test]
    fn block_parameter_exhaustion_does_not_partially_allocate() {
        let mut function = function();
        function.next_value = u64::from(u32::MAX);
        assert_eq!(
            function.new_block_with_params(vec![Type::I32, Type::I64]),
            Err(DialectBuildError::IdentityExhausted(
                DialectIdentityDomain::Value
            ))
        );
        assert_eq!(function.next_value, u64::from(u32::MAX));
        assert_eq!(function.next_block, 1);
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(
            function.new_block_with_params(vec![Type::I64]),
            Ok((BlockId(1), vec![ValueId(u32::MAX)]))
        );
    }

    #[test]
    fn duplicate_block_request_is_rejected_before_allocating_parameters() {
        let mut function = function();
        function.blocks.push(DialectBlock::new(BlockId(1)));
        assert_eq!(
            function.new_block_with_params(vec![Type::I32]),
            Err(DialectBuildError::DuplicateBlock(BlockId(1)))
        );
        assert_eq!(function.next_value, 0);
        assert_eq!(function.next_block, 1);
        assert_eq!(function.blocks.len(), 2);
    }

    #[test]
    fn append_uses_block_identity_and_rejects_missing_or_duplicate_blocks() {
        let mut function = function();
        function.blocks[0].id = BlockId(17);
        assert_eq!(
            append(&mut function, BlockId(0)),
            Err(DialectBuildError::MissingBlock(BlockId(0)))
        );
        assert!(function.ops.is_empty());
        assert_eq!(append(&mut function, BlockId(17)), Ok(OpId(0)));
        assert_eq!(function.blocks[0].ops, [OpId(0)]);
        function.blocks.push(DialectBlock::new(BlockId(17)));
        assert_eq!(
            append(&mut function, BlockId(17)),
            Err(DialectBuildError::DuplicateBlock(BlockId(17)))
        );
        assert_eq!(function.ops.len(), 1);
        assert!(function.blocks[1].ops.is_empty());
    }
}
