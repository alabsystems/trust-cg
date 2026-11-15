// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Let the wasm lane share frame bytes between a function's local arrays.
//!
//! The wasm lane places every fixed `Alloca` in the shadow-stack frame and
//! lets two of them share bytes when, wherever one is allocated, no value
//! derived from the other is live; an `Alloca` whose pointer may be captured
//! (stored to memory, passed to a callee that may keep it) is pinned for the
//! whole activation (`trust-cg-codegen` `wasm/lower/captures.rs` and
//! `storage.rs`). Three shapes of the MIR lowering defeat that for a local
//! array borrowed as a slice:
//!
//! * a large byte or zero fill is a call to the bridge's external
//!   `__trustcg_array_fill_i8` helper, which the lane must assume captures its
//!   pointer argument;
//! * a slice fat pointer lives in a `{ data, len }` slot, so borrowing the array
//!   stores its address into that slot, which is a capture;
//! * every memory-backed local's `Alloca` sits in the entry block, so all of
//!   them are allocated before any one of them is used.
//!
//! An external fill declaration does not authenticate a helper body. Even a
//! declaration named `__trustcg_array_fill_i8` with the expected signature
//! may bind an arbitrary host, so its call and possible captures stay intact
//! (OD-155). No fill-helper body is inferred here, at any optimization level.
//!
//! [`share_frame_slots`] rewrites the other two shapes into ones with the
//! same trust-ir semantics (the reference interpreter's), after word
//! legalization:
//!
//! * [`forward_private_slots`]: a count-free `Alloca` (in any block) of an
//!   array or tuple used only as the aggregate of write-through `insertfield`s
//!   (results unused) and `extractfield`s of its own type is private: nothing
//!   else can read or write its bytes. When every lane that is read is written
//!   exactly once, by a write that dominates each read of that lane, a read
//!   yields the written value (the single write's latest execution precedes
//!   the read, and SSA dominance makes the value operand's latest execution
//!   that same one), so the read becomes a `copy` of the value. The slot's
//!   writes, including any number of writes to lanes that are never read, and
//!   the `Alloca` are then unobservable and removed.
//! * [`sink_entry_allocas`]: a count-free entry-block `Alloca` moves to the
//!   start of the nearest common dominator of its uses, or of that block's
//!   nearest dominator outside every cycle. The new block runs at most once
//!   per activation and before every use, so the allocation stays exactly one
//!   fresh object reaching the same uses.
//!
//! A shape outside these patterns is left as it was: the pass only ever gives
//! the lane fewer captures and later allocation points, never a different
//! computation. It grants no authority; the lane checks the result like any
//! other module, and the evidence is the wasm32 execution differential.

use std::collections::{HashMap, HashSet};

use trust_ir::analysis::DominatorTree;
use trust_ir::{BlockId, Function, Inst, InstrNode, Module, Ty, ValueId};

/// Apply private-slot forwarding and allocation sinking to each definition.
/// External fill calls remain calls without source-bound implementation custody.
pub(crate) fn share_frame_slots(module: &mut Module) -> Result<(), String> {
    for index in 0..module.functions.len() {
        if module.functions[index].blocks.is_empty() {
            continue;
        }
        let func = &module.functions[index];
        let types = trust_cg_codegen::wasm::value_types(module, func)
            .map_err(|err| format!("[TCG-WASM32-FRAME] `{}`: {err}", func.name))?;
        let lane_tys = lane_types(module, func);
        let func = &mut module.functions[index];
        forward_private_slots(func, &types, &lane_tys);
        sink_entry_allocas(func);
    }
    Ok(())
}

/// The lane type of every field of every aggregate type an `Alloca` in `func`
/// declares, when that aggregate is an array or a tuple (lanes that never
/// overlap). Keyed by the aggregate type.
fn lane_types(module: &Module, func: &Function) -> HashMap<Ty, Vec<Ty>> {
    let mut out = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let Inst::Alloca {
            ty, count: None, ..
        } = &node.inst
        else {
            continue;
        };
        let lanes = match ty {
            Ty::Array(elem, n) => match module.ty(*elem) {
                Some(elem) if *n <= 64 => vec![elem.clone(); *n as usize],
                _ => continue,
            },
            Ty::Tuple(tys) => tys.clone(),
            _ => continue,
        };
        out.insert(ty.clone(), lanes);
    }
    out
}

/// Every block index of `func` keyed by its id.
fn block_index(func: &Function) -> HashMap<BlockId, usize> {
    func.blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect()
}

/// Forward the lanes of private single-write slots (module docs).
fn forward_private_slots(
    func: &mut Function,
    types: &HashMap<ValueId, Ty>,
    lane_tys: &HashMap<Ty, Vec<Ty>>,
) {
    if lane_tys.is_empty() {
        return;
    }
    // Candidate slots: count-free `Alloca`s of an array/tuple type.
    let mut slot_ty: HashMap<ValueId, Ty> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let (
            Inst::Alloca {
                ty, count: None, ..
            },
            [r],
        ) = (&node.inst, node.results.as_slice())
        {
            if lane_tys.contains_key(ty) {
                slot_ty.insert(*r, ty.clone());
            }
        }
    }
    if slot_ty.is_empty() {
        return;
    }
    // Every use of a candidate must be as the aggregate of an insert (result
    // unused, value not the slot) or extract of the slot's own type.
    let mut used: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst.visit_value_operands(|v| {
            used.insert(v);
        });
    }
    let mut rejected: HashSet<ValueId> = HashSet::new();
    // (slot, lane) -> the one write: (block index, node index, value).
    let mut writes: HashMap<(ValueId, u32), Vec<(usize, usize, ValueId)>> = HashMap::new();
    // slot -> reads: (block index, node index, lane).
    let mut reads: HashMap<ValueId, Vec<(usize, usize, u32)>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            match &node.inst {
                Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } if slot_ty.contains_key(aggregate) => {
                    let result_used = node.results.iter().any(|r| used.contains(r));
                    if slot_ty[aggregate] != *ty || result_used || value == aggregate {
                        rejected.insert(*aggregate);
                    } else {
                        writes
                            .entry((*aggregate, *field))
                            .or_default()
                            .push((bi, ni, *value));
                    }
                    if slot_ty.contains_key(value) {
                        rejected.insert(*value);
                    }
                }
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if slot_ty.contains_key(aggregate) => {
                    if slot_ty[aggregate] != *ty {
                        rejected.insert(*aggregate);
                    } else {
                        reads.entry(*aggregate).or_default().push((bi, ni, *field));
                    }
                }
                other => other.visit_value_operands(|v| {
                    if slot_ty.contains_key(&v) {
                        rejected.insert(v);
                    }
                }),
            }
        }
    }
    let dom = DominatorTree::new(func);
    if !dom.is_well_formed() {
        return;
    }
    let ids: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();
    // The copies to make: (block index, node index) -> (lane type, value).
    let mut copies: HashMap<(usize, usize), (Ty, ValueId)> = HashMap::new();
    // The writes and allocas to delete: (block index, node index).
    let mut dead: HashSet<(usize, usize)> = HashSet::new();
    let slots: Vec<ValueId> = {
        let mut s: Vec<ValueId> = slot_ty.keys().copied().collect();
        s.sort_by_key(|v| v.index());
        s
    };
    for slot in slots {
        if rejected.contains(&slot) {
            continue;
        }
        let lanes = &lane_tys[&slot_ty[&slot]];
        let slot_reads = reads.get(&slot).map_or(&[][..], Vec::as_slice);
        let mut planned: Vec<((usize, usize), (Ty, ValueId))> = Vec::new();
        let mut all = true;
        for &(rb, rn, lane) in slot_reads {
            let one = match writes.get(&(slot, lane)).map(Vec::as_slice) {
                Some([one]) => *one,
                _ => {
                    all = false;
                    break;
                }
            };
            let (wb, wn, value) = one;
            let dominated = if wb == rb {
                wn < rn
            } else {
                dom.strictly_dominates(ids[wb], ids[rb])
            };
            let lane_ty = lanes.get(lane as usize);
            if !dominated || lane_ty.is_none() || types.get(&value) != lane_ty {
                all = false;
                break;
            }
            planned.push(((rb, rn), (lane_ty.cloned().unwrap_or(Ty::Unit), value)));
        }
        if !all {
            continue;
        }
        copies.extend(planned);
        for ((s, _), list) in &writes {
            if *s == slot {
                dead.extend(list.iter().map(|&(b, n, _)| (b, n)));
            }
        }
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if matches!(node.inst, Inst::Alloca { .. }) && node.results.first() == Some(&slot) {
                    dead.insert((bi, ni));
                }
            }
        }
    }
    if copies.is_empty() && dead.is_empty() {
        return;
    }
    for (bi, block) in func.blocks.iter_mut().enumerate() {
        let mut body = Vec::with_capacity(block.body.len());
        for (ni, mut node) in block.body.drain(..).enumerate() {
            if dead.contains(&(bi, ni)) {
                continue;
            }
            if let Some((ty, operand)) = copies.remove(&(bi, ni)) {
                node.inst = Inst::Copy { ty, operand };
            }
            body.push(node);
        }
        block.body = body;
    }
}

/// The successor blocks of a terminator, or `None` for a terminator whose
/// edges this pass does not model.
fn successors(inst: &Inst) -> Option<Vec<BlockId>> {
    match inst {
        Inst::Br { target, .. } => Some(vec![*target]),
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => Some(vec![*then_target, *else_target]),
        Inst::Switch { default, cases, .. } => {
            let mut out = vec![*default];
            out.extend(cases.iter().map(|c| c.target));
            Some(out)
        }
        Inst::Return { .. } | Inst::Unreachable => Some(Vec::new()),
        _ => None,
    }
}

/// Whether each block (by index) lies on a cycle of the CFG, or `None` when a
/// block ends in a terminator [`successors`] does not model.
fn cyclic_blocks(func: &Function, index: &HashMap<BlockId, usize>) -> Option<Vec<bool>> {
    let n = func.blocks.len();
    let mut succ: Vec<Vec<usize>> = Vec::with_capacity(n);
    for block in &func.blocks {
        let term = block.body.last()?;
        let targets = successors(&term.inst)?;
        let mut s = Vec::with_capacity(targets.len());
        for t in targets {
            s.push(*index.get(&t)?);
        }
        succ.push(s);
    }
    // Iterative Tarjan: a block is cyclic when its strongly connected
    // component has two or more blocks or it has a self edge.
    let mut idx = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut cyclic = vec![false; n];
    let mut counter = 0usize;
    for root in 0..n {
        if idx[root] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        idx[root] = counter;
        low[root] = counter;
        counter += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (v, ref mut next)) = work.last_mut() {
            if *next < succ[v].len() {
                let w = succ[v][*next];
                *next += 1;
                if idx[w] == usize::MAX {
                    idx[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(idx[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == idx[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                let self_edge = succ[v].contains(&v);
                if component.len() > 1 || self_edge {
                    for w in component {
                        cyclic[w] = true;
                    }
                }
            }
        }
    }
    Some(cyclic)
}

/// Sink count-free entry-block `Alloca`s toward their uses (module docs).
fn sink_entry_allocas(func: &mut Function) {
    let index = block_index(func);
    let Some(&entry) = index.get(&func.entry) else {
        return;
    };
    let Some(cyclic) = cyclic_blocks(func, &index) else {
        return;
    };
    if cyclic[entry] {
        return;
    }
    let dom = DominatorTree::new(func);
    if !dom.is_well_formed() {
        return;
    }
    let ids: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();
    let parent = |b: usize| -> Option<usize> {
        let p = dom.immediate_dominator(ids[b])?;
        index.get(&p).copied()
    };
    let nearest_common = |a: usize, b: usize| -> Option<usize> {
        let mut ancestors = HashSet::new();
        let mut x = Some(a);
        while let Some(v) = x {
            ancestors.insert(v);
            x = parent(v);
        }
        let mut y = Some(b);
        while let Some(v) = y {
            if ancestors.contains(&v) {
                return Some(v);
            }
            y = parent(v);
        }
        None
    };
    // The blocks using each value.
    let mut use_blocks: HashMap<ValueId, Vec<usize>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for node in &block.body {
            node.inst.visit_value_operands(|v| {
                let list = use_blocks.entry(v).or_default();
                if list.last() != Some(&bi) {
                    list.push(bi);
                }
            });
        }
    }
    let mut moves: Vec<(usize, usize)> = Vec::new();
    for (ni, node) in func.blocks[entry].body.iter().enumerate() {
        let (Inst::Alloca { count: None, .. }, [a]) = (&node.inst, node.results.as_slice()) else {
            continue;
        };
        let Some(blocks) = use_blocks.get(a) else {
            continue;
        };
        if blocks.iter().any(|&b| !dom.is_reachable(ids[b])) {
            continue;
        }
        let mut target = blocks[0];
        for &b in &blocks[1..] {
            match nearest_common(target, b) {
                Some(t) => target = t,
                None => {
                    target = entry;
                    break;
                }
            }
        }
        while target != entry && cyclic[target] {
            match parent(target) {
                Some(p) => target = p,
                None => {
                    target = entry;
                    break;
                }
            }
        }
        if target != entry {
            moves.push((ni, target));
        }
    }
    if moves.is_empty() {
        return;
    }
    let moved: HashSet<usize> = moves.iter().map(|&(ni, _)| ni).collect();
    let mut sunk: HashMap<usize, Vec<InstrNode>> = HashMap::new();
    let entry_body = std::mem::take(&mut func.blocks[entry].body);
    let mut kept = Vec::with_capacity(entry_body.len());
    let target_of: HashMap<usize, usize> = moves.into_iter().collect();
    for (ni, node) in entry_body.into_iter().enumerate() {
        if moved.contains(&ni) {
            sunk.entry(target_of[&ni]).or_default().push(node);
        } else {
            kept.push(node);
        }
    }
    func.blocks[entry].body = kept;
    for (target, nodes) in sunk {
        let body = &mut func.blocks[target].body;
        let rest = std::mem::take(body);
        body.extend(nodes);
        body.extend(rest);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, Constant, FuncId, FuncTy};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }

    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }

    fn def(inst: Inst, result: u32) -> InstrNode {
        InstrNode::new(inst).with_result(v(result))
    }

    fn alloca(ty: Ty, result: u32) -> InstrNode {
        def(
            Inst::Alloca {
                ty,
                count: None,
                align: None,
            },
            result,
        )
    }

    fn konst(ty: Ty, value: i128, result: u32) -> InstrNode {
        def(
            Inst::Const {
                ty,
                value: Constant::Int(value),
            },
            result,
        )
    }

    fn call(callee: FuncId, args: &[u32]) -> InstrNode {
        InstrNode::new(Inst::Call {
            callee,
            args: args.iter().map(|&a| v(a)).collect(),
        })
    }

    fn insert(ty: &Ty, aggregate: u32, field: u32, value: u32, result: u32) -> InstrNode {
        def(
            Inst::InsertField {
                ty: ty.clone(),
                aggregate: v(aggregate),
                field,
                value: v(value),
            },
            result,
        )
    }

    fn extract(ty: &Ty, aggregate: u32, field: u32, result: u32) -> InstrNode {
        def(
            Inst::ExtractField {
                ty: ty.clone(),
                aggregate: v(aggregate),
                field,
            },
            result,
        )
    }

    fn br(target: u32) -> InstrNode {
        InstrNode::new(Inst::Br {
            target: b(target),
            args: vec![],
        })
    }

    fn ret() -> InstrNode {
        InstrNode::new(Inst::Return { values: vec![] })
    }

    fn block(id: u32, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> Block {
        let mut blk = Block::new(b(id));
        blk.params = params;
        blk.body = body;
        blk
    }

    fn function(module: &mut Module, name: &str, params: Vec<Ty>, blocks: Vec<Block>) -> FuncId {
        let ty = module
            .add_func_type(FuncTy {
                params,
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let id = FuncId::new(module.functions.len() as u32);
        let mut f = Function::new(id, name, ty, b(0));
        f.blocks = blocks;
        module
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        id
    }

    fn fill_helper(module: &mut Module) -> FuncId {
        function(
            module,
            "__trustcg_array_fill_i8",
            vec![Ty::Ptr, Ty::I64, Ty::I32],
            vec![],
        )
    }

    fn insts(func: &Function, block: usize) -> Vec<&Inst> {
        func.blocks[block].body.iter().map(|n| &n.inst).collect()
    }

    /// Run [`forward_private_slots`] on `module.functions[index]`.
    fn forward(module: &mut Module, index: usize) {
        let func = module.functions[index].clone();
        let types = trust_cg_codegen::wasm::value_types(module, &func).unwrap();
        let lanes = lane_types(module, &func);
        forward_private_slots(&mut module.functions[index], &types, &lanes);
    }

    /// Both the formerly rewritten positive constant count and the runtime
    /// count remain external calls at the actual bridge frame entry.
    #[test]
    fn unauthenticated_byte_fill_with_constant_or_runtime_count_is_kept() {
        let mut m = Module::new("m");
        let helper = fill_helper(&mut m);
        let body = vec![
            alloca(Ty::I8, 1),
            konst(Ty::I64, 0, 2),
            konst(Ty::I32, 600, 3),
            call(helper, &[1, 2, 3]),
            call(helper, &[1, 2, 0]),
            ret(),
        ];
        let params = vec![(v(0), Ty::I32)];
        function(&mut m, "f", vec![Ty::I32], vec![block(0, params, body)]);
        let source = m.clone();
        share_frame_slots(&mut m).expect("the bridge frame entry retains imports");
        assert_eq!(m, source, "preserve the complete source and import");
        let f = &m.functions[1];
        let got = insts(f, 0);
        assert!(matches!(
            got[3],
            Inst::Call { callee, args } if *callee == helper && args == &[v(1), v(2), v(3)]
        ));
        assert!(
            matches!(got[4], Inst::Call { callee, args } if *callee == helper && args == &[v(1), v(2), v(0)])
        );
        assert!(!got.iter().any(|inst| matches!(inst, Inst::MemSet { .. })));
    }

    /// A declaration grants no behavior even for a zero or negative count.
    #[test]
    fn byte_fill_with_nonpositive_count_is_kept() {
        for count in [0, -1] {
            let mut m = Module::new("m");
            let helper = fill_helper(&mut m);
            let body = vec![
                alloca(Ty::I8, 1),
                konst(Ty::I64, 0, 2),
                konst(Ty::I32, count, 3),
                call(helper, &[1, 2, 3]),
                ret(),
            ];
            function(&mut m, "f", vec![], vec![block(0, vec![], body)]);
            let source = m.clone();
            share_frame_slots(&mut m).expect("the bridge frame entry retains imports");
            assert_eq!(m, source, "preserve source for count {count}");
            assert!(matches!(insts(&m.functions[1], 0)[3], Inst::Call { .. }));
            assert!(
                !insts(&m.functions[1], 0)
                    .iter()
                    .any(|inst| matches!(inst, Inst::MemSet { .. }))
            );
        }
    }

    /// A no-op host is a legitimate implementation of this ordinary import.
    /// It would leave the initialized word zero; the former name-only rewrite
    /// would change its first byte to seven. This checks retention through the
    /// real bridge frame entry, not host execution or proof authority.
    #[test]
    fn a_foreign_byte_fill_no_op_host_shape_is_retained_by_the_bridge_frame_entry() {
        let mut m = trust_ir::parser::parse_module(
            "module \"foreign-byte-fill\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             functy.0 = (ptr, i64, i32) -> ()\nfuncty.1 = () -> (i32)\n\n\
             fn @__trustcg_array_fill_i8(functy.0) {\n}\n\n\
             fn @probe(functy.1) {\nbb0():\n\
             \x20   %0 = alloca i32, align 4\n\
             \x20   %1 = const i32 0\n\
             \x20   store i32 %1, ptr %0\n\
             \x20   %2 = const i64 7\n\
             \x20   %3 = const i32 1\n\
             \x20   call @func.0(%0, %2, %3)\n\
             \x20   %4 = load i32, ptr %0\n\
             \x20   ret %4\n}\n",
        )
        .expect("parse the actual ordinary-import shape");
        let source = m.clone();
        share_frame_slots(&mut m).expect("the bridge frame entry retains the foreign call");
        assert_eq!(m, source, "preserve the complete initialized-memory source");
        assert!(m.functions[0].is_declaration());
        let probe = m.function_by_name("probe").expect("the original probe");
        let got = insts(probe, 0);
        assert_eq!(
            got.iter()
                .filter(|inst| matches!(inst, Inst::Call { .. }))
                .count(),
            1
        );
        assert!(
            matches!(got[5], Inst::Call { callee, args } if *callee == m.functions[0].id && args == &[v(0), v(2), v(3)])
        );
        assert!(!got.iter().any(|inst| matches!(inst, Inst::MemSet { .. })));
    }

    fn pair_ty(m: &mut Module) -> Ty {
        let elem = m.add_type(Ty::I32).expect("Module::add_type: test fixture");
        Ty::Array(elem, 2)
    }

    /// The slice-borrow shape: both lanes written once, read in a dominated
    /// block. The reads become copies and the slot disappears.
    #[test]
    fn private_single_write_slot_is_forwarded_and_removed() {
        let mut m = Module::new("m");
        let pair = pair_ty(&mut m);
        let b0 = vec![
            alloca(pair.clone(), 1),
            insert(&pair, 1, 0, 0, 2),
            konst(Ty::I32, 7, 3),
            insert(&pair, 1, 1, 3, 4),
            br(1),
        ];
        let b1 = vec![extract(&pair, 1, 0, 5), extract(&pair, 1, 1, 6), ret()];
        let blocks = vec![block(0, vec![(v(0), Ty::I32)], b0), block(1, vec![], b1)];
        function(&mut m, "f", vec![Ty::I32], blocks);
        forward(&mut m, 0);
        let f = &m.functions[0];
        assert!(
            !f.blocks[0]
                .body
                .iter()
                .any(|n| matches!(n.inst, Inst::Alloca { .. } | Inst::InsertField { .. }))
        );
        let got = insts(f, 1);
        assert!(matches!(got[0], Inst::Copy { ty: Ty::I32, operand } if *operand == v(0)));
        assert!(matches!(got[1], Inst::Copy { ty: Ty::I32, operand } if *operand == v(3)));
    }

    /// A slot whose address escapes (passed to a call), whose lane is written
    /// twice, or whose read precedes the write is left unchanged.
    #[test]
    fn slot_that_escapes_or_is_rewritten_or_read_first_is_kept() {
        for case in 0..3 {
            let mut m = Module::new("m");
            let pair = pair_ty(&mut m);
            let sink = function(&mut m, "sink", vec![Ty::Ptr], vec![]);
            let mut b0 = vec![alloca(pair.clone(), 1)];
            if case == 2 {
                b0.push(extract(&pair, 1, 0, 5));
            }
            b0.push(insert(&pair, 1, 0, 0, 2));
            if case == 1 {
                b0.push(insert(&pair, 1, 0, 0, 3));
            }
            if case == 0 {
                b0.push(call(sink, &[1]));
            }
            b0.push(extract(&pair, 1, 0, 6));
            b0.push(ret());
            function(
                &mut m,
                "f",
                vec![Ty::I32],
                vec![block(0, vec![(v(0), Ty::I32)], b0)],
            );
            let before = format!("{:?}", m.functions[1].blocks);
            forward(&mut m, 1);
            assert_eq!(
                format!("{:?}", m.functions[1].blocks),
                before,
                "case {case}"
            );
        }
    }

    /// An entry `Alloca` used only in a later acyclic block moves there; one
    /// used in a loop stops at the loop's nearest acyclic dominator; one used
    /// in the entry stays.
    #[test]
    fn entry_alloca_sinks_to_nearest_acyclic_dominator_of_its_uses() {
        let mut m = Module::new("m");
        let sink = function(&mut m, "sink", vec![Ty::Ptr], vec![]);
        // bb0 -> bb1 -> bb2 (bb2 -> bb2 | bb3) -> bb3.
        let b0 = vec![
            alloca(Ty::I8, 1),
            alloca(Ty::I8, 2),
            alloca(Ty::I8, 3),
            call(sink, &[3]),
            br(1),
        ];
        let b1 = vec![call(sink, &[1]), br(2)];
        let b2 = vec![
            call(sink, &[2]),
            InstrNode::new(Inst::CondBr {
                cond: v(0),
                then_target: b(2),
                then_args: vec![],
                else_target: b(3),
                else_args: vec![],
            }),
        ];
        let blocks = vec![
            block(0, vec![(v(0), Ty::Bool)], b0),
            block(1, vec![], b1),
            block(2, vec![], b2),
            block(3, vec![], vec![ret()]),
        ];
        function(&mut m, "f", vec![Ty::Bool], blocks);
        let f = &mut m.functions[1];
        sink_entry_allocas(f);
        let allocas = |bi: usize| -> Vec<ValueId> {
            f.blocks[bi]
                .body
                .iter()
                .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
                .map(|n| n.results[0])
                .collect()
        };
        assert_eq!(allocas(0), vec![v(3)]);
        assert_eq!(allocas(1), vec![v(1), v(2)]);
        assert!(allocas(2).is_empty());
        assert!(matches!(f.blocks[1].body[0].inst, Inst::Alloca { .. }));
    }
}
