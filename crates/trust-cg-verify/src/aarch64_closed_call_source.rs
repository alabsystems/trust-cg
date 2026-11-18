// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source shape for a defined call followed by an unreachable terminator.
//! A closed normal successor chain has no `Return` edge. Ordinary calls in
//! that chain may have effects, fail to return, or unwind. Neither checking
//! this graph nor identifying its body establishes any of those outcomes.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::inst::Inst;
use trust_ir::proof::ProofDigest;
use trust_ir::{Block, BlockId, CallingConv, FuncId, FuncTy, Function, Linkage, Module};

#[derive(Debug)]
pub(super) struct CheckedClosedSourceCall<'a> {
    module: &'a Module,
    caller: &'a Function,
    callee: &'a Function,
    terminal_site: (BlockId, usize, usize),
    callee_calls: Vec<&'a str>,
}

impl<'a> CheckedClosedSourceCall<'a> {
    pub(super) fn caller_name(&self) -> &'a str {
        &self.caller.name
    }

    pub(super) fn callee_name(&self) -> &'a str {
        &self.callee.name
    }

    pub(super) fn callee_calls(&self) -> &[&'a str] {
        &self.callee_calls
    }

    pub(super) fn callee_call_count(&self) -> usize {
        self.callee_calls.len()
    }

    /// Source block ID, ordinary call index, and unreachable terminator index.
    pub(super) fn caller_terminal_site(&self) -> (BlockId, usize, usize) {
        self.terminal_site
    }

    /// Identity of the exact module, including its declarations and type table.
    /// The digest is not a proof of validation or producer authority.
    pub(super) fn module_body_digest(&self) -> ProofDigest {
        self.module.stable_digest()
    }
}

pub(super) fn bind(
    module: &Module,
    caller: FuncId,
    callee: FuncId,
) -> Option<CheckedClosedSourceCall<'_>> {
    if caller == callee {
        return None;
    }
    let caller = definition(module, caller)?;
    let callee = definition(module, callee)?;
    let signature = ordinary_void_signature(module, callee)?;
    let terminal_site = caller_terminal_site(caller, callee.id, signature.params.len())?;
    let callee_calls = closed_normal_calls(module, callee)?;
    Some(CheckedClosedSourceCall {
        module,
        caller,
        callee,
        terminal_site,
        callee_calls,
    })
}

fn unique_function(module: &Module, id: FuncId) -> Option<&Function> {
    let function = module.function_by_id(id)?;
    (!function.name.is_empty()
        && module
            .functions
            .iter()
            .filter(|other| other.id == id || other.name == function.name)
            .count()
            == 1)
        .then_some(function)
}

fn definition(module: &Module, id: FuncId) -> Option<&Function> {
    let function = unique_function(module, id)?;
    (!function.blocks.is_empty()
        && matches!(
            function.linkage,
            Linkage::External | Linkage::Internal | Linkage::Private
        ))
    .then_some(function)
}

fn ordinary_void_signature<'a>(module: &'a Module, function: &Function) -> Option<&'a FuncTy> {
    let signature = module.func_type(function.ty)?;
    (function.calling_conv == CallingConv::C
        && signature.abi.is_none()
        && !signature.is_vararg
        && signature.returns.is_empty())
    .then_some(signature)
}

fn block_table(function: &Function) -> Option<BTreeMap<BlockId, &Block>> {
    let blocks: BTreeMap<_, _> = function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect();
    (blocks.len() == function.blocks.len() && blocks.contains_key(&function.entry))
        .then_some(blocks)
}

fn caller_terminal_site(
    caller: &Function,
    callee: FuncId,
    arg_count: usize,
) -> Option<(BlockId, usize, usize)> {
    let blocks = block_table(caller)?;
    let mut normal_edges = BTreeMap::new();
    let mut site = None;
    for (&block_id, block) in &blocks {
        let (terminator, body) = block.body.split_last()?;
        let successors: Vec<_> = match &terminator.inst {
            Inst::Br { target, .. } => vec![*target],
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => vec![*then_target, *else_target],
            Inst::Switch { default, cases, .. } => std::iter::once(*default)
                .chain(cases.iter().map(|case| case.target))
                .collect(),
            Inst::Return { .. } | Inst::Unreachable => Vec::new(),
            _ => return None,
        };
        if successors.iter().any(|id| !blocks.contains_key(id)) {
            return None;
        }
        normal_edges.insert(block_id, successors);
        for (index, node) in body.iter().enumerate() {
            match &node.inst {
                Inst::Call {
                    callee: target,
                    args,
                } if *target == callee => {
                    if site.is_some()
                        || index.checked_add(1)? != body.len()
                        || !matches!(terminator.inst, Inst::Unreachable)
                        || args.len() != arg_count
                        || !node.results.is_empty()
                        || !terminator.results.is_empty()
                    {
                        return None;
                    }
                    site = Some((block_id, index, body.len()));
                }
                Inst::Call { .. } => {}
                inst if ordinary_instruction(inst) => {}
                _ => return None,
            }
        }
    }
    let site = site?;
    let mut work = vec![caller.entry];
    let mut visited = BTreeSet::new();
    while let Some(block) = work.pop() {
        if block == site.0 {
            return Some(site);
        }
        if visited.insert(block) {
            work.extend(normal_edges.get(&block)?);
        }
    }
    None
}

/// This slice admits a single finite normal chain, including explicit
/// unconditional jumps. It requires every declared block to occur in that
/// chain once. Interleaving arbitrary branches could change the call order;
/// the returned call list is the order along this one normal chain.
fn closed_normal_calls<'a>(module: &'a Module, callee: &Function) -> Option<Vec<&'a str>> {
    let mut blocks = block_table(callee)?;
    let mut block_id = callee.entry;
    let mut calls = Vec::new();
    loop {
        let block = blocks.remove(&block_id)?;
        let (terminator, body) = block.body.split_last()?;
        if !terminator.results.is_empty() {
            return None;
        }
        for node in body {
            match &node.inst {
                Inst::Call { callee, args } => {
                    let external = unique_function(module, *callee)?;
                    let signature = ordinary_void_signature(module, external)?;
                    if external.linkage != Linkage::External
                        || !external.blocks.is_empty()
                        || signature.params.len() != args.len()
                        || !node.results.is_empty()
                    {
                        return None;
                    }
                    calls.push(external.name.as_str());
                }
                inst if ordinary_instruction(inst) => {}
                _ => return None,
            }
        }
        match &terminator.inst {
            Inst::Br { target, args } => {
                if blocks.get(target)?.params.len() != args.len() {
                    return None;
                }
                block_id = *target;
            }
            Inst::Unreachable if blocks.is_empty() => {
                return matches!(body.last()?.inst, Inst::Call { .. }).then_some(calls);
            }
            _ => return None,
        }
    }
}

/// These forms can advance to the next normal instruction or fail. Their
/// presence says nothing about arithmetic results, pointer validity, memory,
/// side effects, or whether any instruction will actually execute.
fn ordinary_instruction(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Alloca { .. }
            | Inst::BinOp { .. }
            | Inst::Cast { .. }
            | Inst::Const { .. }
            | Inst::Copy { .. }
            | Inst::GlobalAddr { .. }
            | Inst::ICmp { .. }
            | Inst::Load {
                volatile: false,
                ..
            }
            | Inst::Store {
                volatile: false,
                ..
            }
    )
}
