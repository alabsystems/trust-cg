// trust-cg-codegen/wasm/locals.rs - local coalescing and function limits
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reusing wasm locals by liveness, and the per-function implementation
//! limits every engine enforces.
//!
//! The lowering binds one local per SSA value and per scratch temporary.
//! [`coalesce`] rewrites a finished function body so that locals of one value
//! type whose live ranges never overlap share an index. It works on the
//! EMITTED code, so it sees every local the lowering (and its helpers)
//! declared:
//!
//! 1. decode the body into instructions and split it into basic blocks at
//!    every structured-control instruction;
//! 2. compute backward liveness of every declared local over that CFG
//!    (`br` to a `loop` label re-enters the loop, to a `block`/`if` label
//!    leaves through its `end`), one local at a time over the blocks it is
//!    live in, so the cost is the size of the live ranges — within a visit
//!    budget, past which the remaining locals live across blocks keep their
//!    own index;
//! 3. give each local the HULL of its liveness in instruction order — every
//!    instruction that reads or writes it, and the first/last instruction of
//!    every block it is live into/out of — which contains every point where
//!    it is live or written;
//! 4. linear-scan the hulls per value type: two locals share an index only
//!    when their hulls are disjoint.
//!
//! Disjoint hulls keep every read's value: a read of `a` sees the last write
//! to `a` on its path, and no write to a sharer can lie between them, because
//! `a` is live there (so inside `a`'s hull) while the sharer's writes are
//! inside the sharer's. A read of `a` that relies on the zero a local starts
//! with makes `a` live at the function's first instruction, so no sharer is
//! written before it.
//!
//! Parameters are never renumbered. A body the decoder does not recognize is
//! left as it is ([`coalesce`] returns `None`), and [`check_limits`] then
//! applies to it unchanged.
//!
//! The coalesced body is a function's BASELINE: what it is emitted with at O0,
//! and when the emission pass (`opt.rs`) has no validated rewrite for it. That pass
//! reuses this module's decoder and [`cfg`].

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use super::encode::{Reloc, ValType, write_uleb128};

/// The BASELINE body of a function (what it is emitted with when the
/// emission pass in `opt.rs` declines or its candidate is not validated) is
/// coalesced only when the function declares at least this many locals: the
/// lane's behaviour before that pass, and all an O0 compile emits. The pass
/// itself, at O1 and above, colours every function.
pub const BASELINE_COALESCE_MIN_LOCALS: usize = 64;

/// The JS-API implementation limits ("Limits" in the WebAssembly JavaScript
/// Interface specification, shared by V8 and wasmparser/wasmtime): a module
/// that exceeds one does not compile in those engines.
pub const MAX_FUNCTION_LOCALS: u64 = 50_000;
/// Parameters of one function type.
pub const MAX_FUNCTION_PARAMS: usize = 1_000;
/// Results of one function type.
pub const MAX_FUNCTION_RESULTS: usize = 1_000;
/// Bytes of one function body.
pub const MAX_FUNCTION_BODY_BYTES: u64 = 7_654_321;

/// Block visits (plus predecessor edges followed) [`coalesce`]'s liveness
/// spends on one function before it stops sharing the remaining live-across-
/// blocks locals (each then keeps an index of its own).
const MAX_LIVENESS_VISITS: usize = 1 << 26;

/// A rewritten body.
pub struct Coalesced {
    /// Declared (non-parameter) locals, in index order.
    pub declared: Vec<ValType>,
    /// The code with every local index renumbered.
    pub code: Vec<u8>,
    /// Relocations, moved with the bytes they patch.
    pub relocs: Vec<Reloc>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Plain,
    Get(u32),
    Set(u32),
    Tee(u32),
    Block,
    Loop,
    If,
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable,
    Return,
    Unreachable,
}

pub(super) struct Ins {
    pub start: usize,
    pub end: usize,
    pub kind: Kind,
}

fn uleb(code: &[u8], pos: &mut usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut shift = 0;
    loop {
        let b = *code.get(*pos)?;
        *pos += 1;
        if shift < 64 {
            v |= u64::from(b & 0x7f) << shift;
        }
        if b & 0x80 == 0 {
            return Some(v);
        }
        shift += 7;
        if shift > 70 {
            return None;
        }
    }
}

fn skip(code: &[u8], pos: &mut usize, n: usize) -> Option<()> {
    *pos = pos.checked_add(n)?;
    (*pos <= code.len()).then_some(())
}

fn blocktype(code: &[u8], pos: &mut usize) -> Option<()> {
    match *code.get(*pos)? {
        0x40 | 0x7f | 0x7e | 0x7d | 0x7c | 0x7b | 0x70 | 0x6f => skip(code, pos, 1),
        _ => uleb(code, pos).map(|_| ()),
    }
}

fn memarg(code: &[u8], pos: &mut usize) -> Option<()> {
    let align = uleb(code, pos)?;
    if align & 0x40 != 0 {
        uleb(code, pos)?;
    }
    uleb(code, pos).map(|_| ())
}

/// Decode `code` into instructions, plus each `br_table`'s depths.
pub(super) fn decode(code: &[u8]) -> Option<(Vec<Ins>, Vec<Vec<u32>>)> {
    let mut out = Vec::new();
    let mut tables = Vec::new();
    let mut pos = 0usize;
    let u32_of = |v: u64| u32::try_from(v).ok();
    while pos < code.len() {
        let start = pos;
        let opcode = code[pos];
        pos += 1;
        let kind = match opcode {
            0x00 => Kind::Unreachable,
            0x01 | 0x1a | 0x1b | 0x45..=0xc4 | 0xd1 => Kind::Plain,
            0x02 => {
                blocktype(code, &mut pos)?;
                Kind::Block
            }
            0x03 => {
                blocktype(code, &mut pos)?;
                Kind::Loop
            }
            0x04 => {
                blocktype(code, &mut pos)?;
                Kind::If
            }
            0x05 => Kind::Else,
            0x0b => Kind::End,
            0x0c => Kind::Br(u32_of(uleb(code, &mut pos)?)?),
            0x0d => Kind::BrIf(u32_of(uleb(code, &mut pos)?)?),
            0x0e => {
                let n = uleb(code, &mut pos)?;
                let mut depths = Vec::new();
                for _ in 0..=n {
                    depths.push(u32_of(uleb(code, &mut pos)?)?);
                }
                tables.push(depths);
                Kind::BrTable
            }
            0x0f => Kind::Return,
            0x10 | 0x23 | 0x24 | 0x25 | 0x26 | 0xd2 => {
                uleb(code, &mut pos)?;
                Kind::Plain
            }
            0x11 => {
                uleb(code, &mut pos)?;
                uleb(code, &mut pos)?;
                Kind::Plain
            }
            0x1c => {
                let n = usize::try_from(uleb(code, &mut pos)?).ok()?;
                skip(code, &mut pos, n)?;
                Kind::Plain
            }
            0x20 => Kind::Get(u32_of(uleb(code, &mut pos)?)?),
            0x21 => Kind::Set(u32_of(uleb(code, &mut pos)?)?),
            0x22 => Kind::Tee(u32_of(uleb(code, &mut pos)?)?),
            0x28..=0x3e => {
                memarg(code, &mut pos)?;
                Kind::Plain
            }
            0x3f | 0x40 => {
                uleb(code, &mut pos)?;
                Kind::Plain
            }
            0x41 | 0x42 => {
                // sleb: same byte structure as uleb.
                uleb(code, &mut pos)?;
                Kind::Plain
            }
            0x43 => {
                skip(code, &mut pos, 4)?;
                Kind::Plain
            }
            0x44 => {
                skip(code, &mut pos, 8)?;
                Kind::Plain
            }
            0xd0 => {
                skip(code, &mut pos, 1)?;
                Kind::Plain
            }
            0xfc => {
                match uleb(code, &mut pos)? {
                    0..=7 => {}
                    9 | 11 | 13 | 15 | 16 | 17 => {
                        uleb(code, &mut pos)?;
                    }
                    8 | 10 | 12 | 14 => {
                        uleb(code, &mut pos)?;
                        uleb(code, &mut pos)?;
                    }
                    _ => return None,
                }
                Kind::Plain
            }
            _ => return None,
        };
        out.push(Ins {
            start,
            end: pos,
            kind,
        });
    }
    Some((out, tables))
}

/// The basic blocks of a decoded body and the edges between them: every
/// control instruction is its own block, and a run of other instructions
/// between them is one block. `br` to a `loop` label re-enters the loop at its
/// `loop` instruction; to a `block`/`if` label it leaves through its `end`.
pub(super) struct Cfg {
    /// The block of every instruction.
    pub block_of: Vec<usize>,
    /// First instruction of every block.
    pub first: Vec<usize>,
    /// Last instruction of every block.
    pub last: Vec<usize>,
    /// Successor blocks.
    pub succs: Vec<Vec<usize>>,
    /// Predecessor blocks.
    pub preds: Vec<Vec<usize>>,
}

/// Build the [`Cfg`] of `ins` (with its `br_table` depths); `None` when the
/// structure is unbalanced.
pub(super) fn cfg(ins: &[Ins], tables: &[Vec<u32>]) -> Option<Cfg> {
    let m = ins.len();
    if m == 0 {
        return None;
    }
    // Structure: the matching `end` (and `else`) of every opener, and the
    // label every branch names.
    let mut end_of = vec![usize::MAX; m];
    let mut else_of = vec![usize::MAX; m];
    let mut if_of_else = vec![usize::MAX; m];
    let mut targets: Vec<Vec<usize>> = vec![Vec::new(); m];
    {
        let mut stack: Vec<usize> = Vec::new();
        let mut table = 0usize;
        // Each branch's labels, as the opener each depth names. A depth equal
        // to the stack height names the function body itself: it returns, so
        // it has no successor here. A `block`/`if` label resolves to its
        // `end`, which is only known once seen, so resolution waits.
        let mut pending: Vec<(usize, Vec<usize>)> = Vec::new();
        for (i, x) in ins.iter().enumerate() {
            let depths: Vec<u32> = match x.kind {
                Kind::Block | Kind::Loop | Kind::If => {
                    stack.push(i);
                    continue;
                }
                Kind::Else => {
                    let o = *stack.last()?;
                    if ins[o].kind != Kind::If || else_of[o] != usize::MAX {
                        return None;
                    }
                    else_of[o] = i;
                    if_of_else[i] = o;
                    continue;
                }
                Kind::End => {
                    let o = stack.pop()?;
                    end_of[o] = i;
                    continue;
                }
                Kind::Br(d) | Kind::BrIf(d) => vec![d],
                Kind::BrTable => {
                    let depths = tables.get(table)?.clone();
                    table += 1;
                    depths
                }
                _ => continue,
            };
            let labels = depths
                .iter()
                .filter_map(|&d| {
                    let d = d as usize;
                    (d < stack.len()).then(|| stack[stack.len() - 1 - d])
                })
                .collect();
            pending.push((i, labels));
        }
        if !stack.is_empty() {
            return None;
        }
        for (i, labels) in pending {
            for o in labels {
                targets[i].push(if ins[o].kind == Kind::Loop {
                    o
                } else {
                    end_of[o]
                });
            }
        }
    }

    // Basic blocks: every control instruction is its own block, and a run of
    // other instructions between them is one block.
    let is_control =
        |k: Kind| !matches!(k, Kind::Plain | Kind::Get(_) | Kind::Set(_) | Kind::Tee(_));
    let mut block_of = vec![0usize; m];
    let mut first: Vec<usize> = Vec::new();
    for (i, x) in ins.iter().enumerate() {
        let new = i == 0 || is_control(x.kind) || is_control(ins[i - 1].kind);
        if new {
            first.push(i);
        }
        block_of[i] = first.len() - 1;
    }
    let nb = first.len();
    let last: Vec<usize> = (0..nb)
        .map(|b| if b + 1 < nb { first[b + 1] - 1 } else { m - 1 })
        .collect();
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for b in 0..nb {
        let i = last[b];
        let next = (b + 1 < nb).then_some(b + 1);
        let s = &mut succs[b];
        match ins[i].kind {
            Kind::Br(_) | Kind::BrTable => s.extend(targets[i].iter().map(|&t| block_of[t])),
            Kind::BrIf(_) => {
                s.extend(targets[i].iter().map(|&t| block_of[t]));
                s.extend(next);
            }
            Kind::If => {
                s.extend(next);
                let e = else_of[i];
                if e != usize::MAX {
                    if e + 1 < m {
                        s.push(block_of[e + 1]);
                    }
                } else {
                    s.push(block_of[end_of[i]]);
                }
            }
            // The end of a `then` arm continues after the `if`'s `end`.
            Kind::Else => s.push(block_of[end_of[if_of_else[i]]]),
            Kind::Return | Kind::Unreachable => {}
            _ => s.extend(next),
        }
    }
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for (b, ss) in succs.iter().enumerate() {
        for &t in ss {
            preds[t].push(b);
        }
    }

    Some(Cfg {
        block_of,
        first,
        last,
        succs,
        preds,
    })
}

/// Coalesce the declared locals of a function body (module docs). `params`
/// is the number of parameters (never renumbered); `declared` the declared
/// locals in index order. `None` when the body cannot be analysed.
pub fn coalesce(
    params: usize,
    declared: &[ValType],
    code: &[u8],
    relocs: &[Reloc],
) -> Option<Coalesced> {
    coalesce_within(params, declared, code, relocs, MAX_LIVENESS_VISITS)
}

/// [`coalesce`] with a liveness budget of `budget` block visits.
fn coalesce_within(
    params: usize,
    declared: &[ValType],
    code: &[u8],
    relocs: &[Reloc],
    budget: usize,
) -> Option<Coalesced> {
    let (ins, tables) = decode(code)?;
    let n = declared.len();
    if n == 0 || ins.is_empty() {
        return None;
    }
    let local = |idx: u32| -> Option<Option<usize>> {
        let idx = usize::try_from(idx).ok()?;
        if idx < params {
            Some(None)
        } else if idx - params < n {
            Some(Some(idx - params))
        } else {
            None
        }
    };

    let Cfg {
        block_of,
        first,
        last,
        preds,
        ..
    } = cfg(&ins, &tables)?;
    let m = ins.len();
    let nb = first.len();

    // Per local: the blocks where it is UPWARD-EXPOSED (read before any
    // write in the block — its uses that liveness propagates backward from)
    // and the blocks that write it; and the hull event of every reference.
    let mut lo = vec![usize::MAX; n];
    let mut hi = vec![0usize; n];
    let touch = |l: usize, at: usize, lo: &mut [usize], hi: &mut [usize]| {
        lo[l] = lo[l].min(at);
        hi[l] = hi[l].max(at);
    };
    let mut exposed: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut writes: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut seen_in = vec![usize::MAX; n];
    let mut written_in = vec![usize::MAX; n];
    for (i, x) in ins.iter().enumerate() {
        let b = block_of[i];
        let (idx, write) = match x.kind {
            Kind::Get(idx) => (idx, false),
            Kind::Set(idx) | Kind::Tee(idx) => (idx, true),
            _ => continue,
        };
        let Some(l) = local(idx)? else { continue };
        if seen_in[l] != b {
            seen_in[l] = b;
            if !write {
                exposed[l].push(b);
            }
        }
        if write && written_in[l] != b {
            written_in[l] = b;
            writes[l].push(b);
        }
        touch(l, i, &mut lo, &mut hi);
    }

    // Backward liveness, one local at a time over the sparse set of blocks
    // it is live in: from each upward-exposed use, through predecessors, up
    // to the blocks that write it. `l` is live into every block reached
    // (touching that block's first instruction) and live out of each of its
    // predecessors (touching their last). This is exactly the classic
    // dataflow fixpoint's live-in/live-out sets, so the hulls are the same;
    // its cost is the total size of the live ranges, not blocks x locals.
    //
    // Past [`MAX_LIVENESS_VISITS`] the remaining upward-exposed locals are
    // given the whole body as their hull — they keep an index of their own,
    // which is sound — while every other local is still coalesced.
    let mut live_mark = vec![usize::MAX; nb];
    let mut write_mark = vec![usize::MAX; nb];
    let mut budget = budget;
    let mut work: Vec<usize> = Vec::new();
    for l in 0..n {
        if exposed[l].is_empty() {
            continue;
        }
        if budget == 0 {
            touch(l, 0, &mut lo, &mut hi);
            touch(l, m - 1, &mut lo, &mut hi);
            continue;
        }
        for &b in &writes[l] {
            write_mark[b] = l;
        }
        work.clear();
        for &b in &exposed[l] {
            if live_mark[b] != l {
                live_mark[b] = l;
                work.push(b);
            }
        }
        while let Some(b) = work.pop() {
            touch(l, first[b], &mut lo, &mut hi);
            for &p in &preds[b] {
                touch(l, last[p], &mut lo, &mut hi);
                if write_mark[p] != l && live_mark[p] != l {
                    live_mark[p] = l;
                    work.push(p);
                }
            }
            budget = budget.saturating_sub(1 + preds[b].len());
            if budget == 0 {
                touch(l, 0, &mut lo, &mut hi);
                touch(l, m - 1, &mut lo, &mut hi);
                break;
            }
        }
    }

    // Linear scan per value type over the hulls.
    let mut order: Vec<usize> = (0..n).filter(|&l| lo[l] != usize::MAX).collect();
    order.sort_by_key(|&l| (lo[l], l));
    let types = [ValType::I32, ValType::I64, ValType::F32, ValType::F64];
    let mut color = vec![usize::MAX; n];
    let mut colors_of: Vec<usize> = vec![0; types.len()];
    for (t, vt) in types.iter().enumerate() {
        let mut active: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
        let mut free: Vec<usize> = Vec::new();
        for &l in order.iter().filter(|&&l| declared[l] == *vt) {
            while let Some(Reverse((e, c))) = active.peek().copied() {
                if e < lo[l] {
                    active.pop();
                    free.push(c);
                } else {
                    break;
                }
            }
            let c = free.pop().unwrap_or_else(|| {
                colors_of[t] += 1;
                colors_of[t] - 1
            });
            color[l] = c;
            active.push(Reverse((hi[l], c)));
        }
    }
    let mut base = vec![0usize; types.len()];
    let mut next = params;
    for t in 0..types.len() {
        base[t] = next;
        next += colors_of[t];
    }
    let new_index = |l: usize| -> usize {
        let t = types.iter().position(|v| *v == declared[l]).unwrap_or(0);
        base[t] + color[l]
    };
    let mut new_declared = Vec::with_capacity(next - params);
    for (t, vt) in types.iter().enumerate() {
        new_declared.extend(std::iter::repeat_n(*vt, colors_of[t]));
    }
    if new_declared.len() >= n {
        return None;
    }

    // Re-encode, moving relocations with their instruction.
    let mut out = Vec::with_capacity(code.len());
    let mut new_start = Vec::with_capacity(m);
    for x in &ins {
        new_start.push(out.len());
        let (op, idx) = match x.kind {
            Kind::Get(i) => (0x20u8, i),
            Kind::Set(i) => (0x21, i),
            Kind::Tee(i) => (0x22, i),
            _ => {
                out.extend_from_slice(&code[x.start..x.end]);
                continue;
            }
        };
        let idx = match local(idx)? {
            None => idx as usize,
            Some(l) => new_index(l),
        };
        out.push(op);
        write_uleb128(&mut out, idx as u64);
    }
    let mut moved = Vec::with_capacity(relocs.len());
    for r in relocs {
        let at = r.offset as usize;
        let k = ins.partition_point(|x| x.start <= at).checked_sub(1)?;
        if matches!(ins[k].kind, Kind::Get(_) | Kind::Set(_) | Kind::Tee(_)) {
            return None;
        }
        let offset = u32::try_from(at - ins[k].start + new_start[k]).ok()?;
        moved.push(Reloc { offset, ..*r });
    }
    Some(Coalesced {
        declared: new_declared,
        code: out,
        relocs: moved,
    })
}

/// Refuse a function an engine would not compile: more than
/// [`MAX_FUNCTION_PARAMS`] parameters, [`MAX_FUNCTION_RESULTS`] results,
/// [`MAX_FUNCTION_LOCALS`] locals (parameters included) or
/// [`MAX_FUNCTION_BODY_BYTES`] body bytes.
pub fn check_limits(
    name: &str,
    params: usize,
    results: usize,
    declared: &[(u32, ValType)],
    code_len: usize,
) -> Result<(), String> {
    if params > MAX_FUNCTION_PARAMS {
        return Err(format!(
            "`{name}` has {params} parameters; engines accept at most {MAX_FUNCTION_PARAMS}"
        ));
    }
    if results > MAX_FUNCTION_RESULTS {
        return Err(format!(
            "`{name}` has {results} results; engines accept at most {MAX_FUNCTION_RESULTS}"
        ));
    }
    let locals = params as u64 + declared.iter().map(|(c, _)| u64::from(*c)).sum::<u64>();
    if locals > MAX_FUNCTION_LOCALS {
        return Err(format!(
            "`{name}` needs {locals} locals (parameters included) after coalescing; engines \
             accept at most {MAX_FUNCTION_LOCALS}"
        ));
    }
    let mut header = Vec::new();
    write_uleb128(&mut header, declared.len() as u64);
    for (c, _) in declared {
        write_uleb128(&mut header, u64::from(*c));
        header.push(0);
    }
    let body = header.len() as u64 + code_len as u64 + 1;
    if body > MAX_FUNCTION_BODY_BYTES {
        return Err(format!(
            "`{name}` has a {body}-byte body; engines accept at most {MAX_FUNCTION_BODY_BYTES}"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::encode::{RelocKind, RelocTarget, write_padded_uleb128};
    use super::*;

    const GET: u8 = 0x20;
    const SET: u8 = 0x21;
    const I64: ValType = ValType::I64;

    /// The local index of every `local.get`/`set`/`tee` in `code`, in order.
    fn local_refs(code: &[u8]) -> Vec<(u8, u32)> {
        let (ins, _) = decode(code).expect("decodes");
        ins.iter()
            .filter_map(|x| match x.kind {
                Kind::Get(i) => Some((0x20, i)),
                Kind::Set(i) => Some((0x21, i)),
                Kind::Tee(i) => Some((0x22, i)),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn sequential_temporaries_share_one_local() {
        // param 0; locals 1..=3 each set from param 0 and read once, in turn.
        let mut code = Vec::new();
        for l in 1..=3u8 {
            code.extend([GET, 0, SET, l, GET, l, 0x1a]);
        }
        code.push(0x00);
        let c = coalesce(1, &[I64, I64, I64], &code, &[]).expect("coalesces");
        assert_eq!(c.declared, vec![I64]);
        assert!(
            local_refs(&c.code)
                .iter()
                .all(|&(op, i)| (op == GET && i == 0) || i == 1)
        );
    }

    #[test]
    fn a_value_live_around_a_back_edge_keeps_its_own_local() {
        // loop { get 1; set 2; get 2; drop; get 0; set 1; get 0; br_if 0 } —
        // local 1 is read at the top of the loop before being written at the
        // bottom, so it is live across every point of the loop body.
        let code = vec![
            0x03, 0x40, GET, 1, SET, 2, GET, 2, 0x1a, GET, 0, SET, 1, GET, 0, 0x0d, 0, 0x0b, 0x00,
        ];
        // `n` equals what coalescing would keep, so no rewrite is offered.
        assert!(coalesce(1, &[I64, I64], &code, &[]).is_none());
    }

    #[test]
    fn a_read_of_the_initial_zero_is_not_given_a_written_sharer() {
        // set 1; get 1; drop; get 2 — local 2 is read without ever being
        // written, so it holds zero; it must not share local 1's index.
        let code = vec![GET, 0, SET, 1, GET, 1, 0x1a, GET, 2, 0x1a, 0x00];
        assert!(coalesce(1, &[I64, I64], &code, &[]).is_none());
        // The other order is fine: 2 is read (as zero) before 1 is written.
        let code = vec![GET, 2, 0x1a, GET, 0, SET, 1, GET, 1, 0x1a, 0x00];
        let c = coalesce(1, &[I64, I64], &code, &[]).expect("coalesces");
        assert_eq!(c.declared, vec![I64]);
    }

    #[test]
    fn relocations_move_with_their_instruction() {
        // 200 short-lived locals, most with two-byte LEB indices, collapse
        // into one: the code shrinks, and the relocated `call` immediate after
        // them must move with it.
        let mut code = Vec::new();
        let mut declared = Vec::new();
        for l in 1..=200u32 {
            code.push(GET);
            code.push(0);
            code.push(SET);
            write_uleb128(&mut code, u64::from(l));
            code.push(GET);
            write_uleb128(&mut code, u64::from(l));
            code.push(0x1a);
            declared.push(I64);
        }
        code.push(0x10);
        let at = code.len() as u32;
        write_padded_uleb128(&mut code, 7);
        code.push(0x00);
        let reloc = Reloc {
            kind: RelocKind::FunctionIndexLeb,
            offset: at,
            target: RelocTarget::Func(7),
            addend: 0,
        };
        let c = coalesce(1, &declared, &code, &[reloc]).expect("coalesces");
        assert_eq!(c.declared, vec![I64]);
        let moved = c.relocs[0].offset as usize;
        assert_eq!(
            c.code[moved - 1],
            0x10,
            "the relocation still follows `call`"
        );
        assert_eq!(&c.code[moved..moved + 5], &[0x87, 0x80, 0x80, 0x80, 0x00]);
    }

    #[test]
    fn past_the_liveness_budget_only_cross_block_locals_keep_their_own_index() {
        // block { get 0; set 1 } get 1; drop; block { get 0; set 2 } get 2;
        // drop; then locals 3 and 4 each written and read within one run.
        let mut code = vec![0x02, 0x40, GET, 0, SET, 1, 0x0b, GET, 1, 0x1a];
        code.extend([0x02, 0x40, GET, 0, SET, 2, 0x0b, GET, 2, 0x1a]);
        code.extend([
            GET, 0, SET, 3, GET, 3, 0x1a, GET, 0, SET, 4, GET, 4, 0x1a, 0x00,
        ]);
        let declared = [I64; 4];
        // Within budget, all four live ranges are disjoint: one local.
        let c = coalesce(1, &declared, &code, &[]).expect("coalesces");
        assert_eq!(c.declared, vec![I64]);
        // Out of budget, locals 1 and 2 (read in a block after the one that
        // writes them) get the whole body as their hull; 3 and 4, whose every
        // reference lies in one block, still share.
        let c = coalesce_within(1, &declared, &code, &[], 0).expect("coalesces");
        assert_eq!(c.declared, vec![I64; 3]);
        // Every other reference is `get 0`: locals 1..=4 are written at
        // references 1, 4, 7 and 10.
        let refs = local_refs(&c.code);
        assert_ne!(
            refs[1].1, refs[4].1,
            "live-across locals keep distinct indices"
        );
        assert_eq!(refs[7].1, refs[10].1, "block-local locals share");
    }

    #[test]
    fn engine_limits_are_named() {
        assert!(
            check_limits("f", 1001, 0, &[], 0)
                .unwrap_err()
                .contains("1001 parameters")
        );
        assert!(
            check_limits("f", 0, 1001, &[], 0)
                .unwrap_err()
                .contains("1001 results")
        );
        assert!(
            check_limits("f", 1, 0, &[(50_000, I64)], 0)
                .unwrap_err()
                .contains("50001 locals")
        );
        assert!(check_limits("f", 1, 0, &[(49_999, I64)], 0).is_ok());
        assert!(check_limits("f", 0, 0, &[], 7_654_400).is_err());
    }
}
