// trust-cg-codegen/wasm/opt/control.rs - control cleanup of the emission pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The control cleanup the emission pass makes before its segment rewrites,
//! on the lowering's own body. The relooper closes every arm with a `br` to
//! the construct the code continues after, and every function with a
//! `return`; where falling through reaches the same place the branch is
//! redundant. Each round:
//!
//! 1. **dead code** — instructions after an unconditional transfer (`br`,
//!    `br_table`, `return`, `unreachable`), or after the `end` of a construct
//!    no path leaves (no fall-through into its `end`, no `if` path to it, no
//!    branch to its label), up to the `else` or `end` that closes their own
//!    construct, whole nested constructs included, are deleted; after such
//!    an `end`, where the stack height there is not the one the next `end`
//!    needs (or that is the function's end and it has results), the first
//!    of them must be `unreachable` and is kept, so the body still
//!    validates;
//! 2. **fall-through branches** — a `br` (or `return`) is deleted when
//!    falling through from it reaches its target: only `end`s and the
//!    skipped `else` arms of `if`s lie between them (never a `loop`'s
//!    label), and the stack height at the branch is the height every `end`
//!    passed requires (the frame's height plus its results), so the branch
//!    discards and moves no value;
//! 3. **unnamed constructs** — a `block` or `loop` no remaining branch names
//!    is unwrapped: its opener and `end` are deleted;
//! 4. **empty `else` arms** — an `else` whose arm holds nothing is deleted;
//! 5. **`br_if`** — `if; br d; end` (no other instruction in the arm, no
//!    value pushed in it, `d >= 1`) becomes `br_if (d - 1)`.
//!
//! Every branch kept is re-encoded with its depth counted over the kept
//! constructs. Rounds repeat while one changes something, up to
//! [`MAX_ROUNDS`].
//!
//! Heights come from this module's own stack accounting (the operand counts
//! of every instruction and the function and type signatures of the module);
//! a body it cannot account for, a block type other than the empty one, and
//! a dead instruction carrying a relocation leave the body as it is. Nothing here
//! is trusted: `trust_cg_verify::wasm_local_tv::validate_control` checks
//! every cleaned body against the body it came from with a lockstep
//! simulation of its own, and a body it refuses is not used.

use trust_cg_verify::wasm_local_tv::TvTypes;

use super::super::encode::{Reloc, write_uleb128};
use super::super::locals::{self, Kind};
use super::Body;

/// Cleanup rounds per body.
const MAX_ROUNDS: usize = 4;

const NONE: usize = usize::MAX;

/// What the cleanup removed or rewrote.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ControlStats {
    /// `br`s deleted because falling through reaches their target.
    pub branches: usize,
    /// `return`s deleted because falling through returns the same values.
    pub returns: usize,
    /// Unreachable instructions deleted.
    pub dead: usize,
    /// `block`s and `loop`s unwrapped.
    pub blocks: usize,
    /// Empty `else` arms deleted.
    pub elses: usize,
    /// `if; br; end` arms turned into `br_if`.
    pub br_ifs: usize,
}

impl ControlStats {
    fn plus(self, o: ControlStats) -> ControlStats {
        ControlStats {
            branches: self.branches + o.branches,
            returns: self.returns + o.returns,
            dead: self.dead + o.dead,
            blocks: self.blocks + o.blocks,
            elses: self.elses + o.elses,
            br_ifs: self.br_ifs + o.br_ifs,
        }
    }

    /// The counts by rule name, for the summary.
    pub(crate) fn by_rule(self) -> [(&'static str, usize); 6] {
        [
            ("br", self.branches),
            ("return", self.returns),
            ("dead", self.dead),
            ("block", self.blocks),
            ("else", self.elses),
            ("br_if", self.br_ifs),
        ]
    }
}

/// Clean `body` (module docs) for a function with `results` results; `None`
/// when nothing changed or the body cannot be accounted for.
pub(crate) fn cleanup(
    results: usize,
    body: &Body,
    types: &dyn TvTypes,
) -> Option<(Body, ControlStats)> {
    let mut cur = body.clone();
    let mut stats = ControlStats::default();
    let mut changed = false;
    for _ in 0..MAX_ROUNDS {
        match round(results, &cur, types)? {
            Some((next, s)) => {
                cur = next;
                stats = stats.plus(s);
                changed = true;
            }
            None => break,
        }
    }
    changed.then_some((cur, stats))
}

fn uleb_at(code: &[u8], mut pos: usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut shift = 0;
    loop {
        let b = *code.get(pos)?;
        pos += 1;
        if shift < 64 {
            v |= u64::from(b & 0x7f) << shift;
        }
        if b & 0x80 == 0 {
            return Some(v);
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
}

/// Operands popped and results pushed by a straight-line instruction.
fn effect(code: &[u8], x: &locals::Ins, types: &dyn TvTypes) -> Option<(usize, usize)> {
    let op = code[x.start];
    Some(match op {
        0x01 => (0, 0),
        0x1a => (1, 0),
        0x1b => (3, 1),
        0x10 => {
            let f = u32::try_from(uleb_at(code, x.start + 1)?).ok()?;
            let sig = types.func(f)?;
            (sig.params.len(), sig.results.len())
        }
        0x11 => {
            let t = u32::try_from(uleb_at(code, x.start + 1)?).ok()?;
            let sig = types.type_at(t)?;
            (sig.params.len() + 1, sig.results.len())
        }
        0x20 | 0x23 => (0, 1),
        0x21 | 0x24 => (1, 0),
        0x22 => (1, 1),
        0x28..=0x35 => (1, 1),
        0x36..=0x3e => (2, 0),
        0x3f => (0, 1),
        0x40 => (1, 1),
        0x41..=0x44 => (0, 1),
        0x45 | 0x50 | 0x67..=0x69 | 0x79..=0x7b | 0x8b..=0x91 | 0x99..=0x9f | 0xa7..=0xc4 => (1, 1),
        0x46..=0x4f | 0x51..=0x66 | 0x6a..=0x78 | 0x7c..=0x8a | 0x92..=0x98 | 0xa0..=0xa6 => (2, 1),
        0xfc => match uleb_at(code, x.start + 1)? {
            0..=7 => (1, 1),
            10 | 11 => (3, 0),
            _ => return None,
        },
        _ => return None,
    })
}

/// The results an opener's `end` leaves: only the empty block type is
/// cleaned (the validator models no other), so `None` for any other.
fn end_arity(code: &[u8], x: &locals::Ins) -> Option<usize> {
    match code.get(x.start + 1)? {
        0x40 => Some(0),
        _ => None,
    }
}

/// Mark the frame a live branch to depth `d` names; `None` past the
/// function.
fn name(frames: &mut [Frame], d: u32) -> Option<()> {
    let k = frames.len().checked_sub(1 + d as usize)?;
    frames[k].named = true;
    Some(())
}

struct Frame {
    opener: usize,
    height: usize,
    results: usize,
    /// No path reaches the current point of the frame (the stack is
    /// polymorphic).
    unreachable: bool,
    /// The frame was opened in unreachable code: all of it is dead.
    dead: bool,
    /// A live branch names the frame's label.
    named: bool,
    /// The `then` arm of an `if` falls through to its `else`.
    then_falls: bool,
    /// The frame became unreachable after the `end` of a construct no path
    /// leaves, whose height is not the one the frame's next `end` needs: the
    /// first dead instruction must be an `unreachable`, which is kept.
    keep_filler: bool,
}

/// One round; `None` when the body cannot be accounted for, `Some(None)`
/// when nothing changes.
fn round(results: usize, body: &Body, types: &dyn TvTypes) -> Option<Option<(Body, ControlStats)>> {
    let code = &body.code;
    let (ins, tables) = locals::decode(code)?;
    let n = ins.len();
    if n == 0 {
        return Some(None);
    }
    // Structure.
    let mut end_of = vec![NONE; n];
    let mut else_of = vec![NONE; n];
    let mut opener_of = vec![NONE; n];
    let mut parent = vec![NONE; n];
    let mut arity = vec![0usize; n];
    let mut table_of = vec![NONE; n];
    {
        let mut stack: Vec<usize> = Vec::new();
        let mut t = 0usize;
        for i in 0..n {
            parent[i] = stack.last().copied().unwrap_or(NONE);
            match ins[i].kind {
                Kind::Block | Kind::Loop | Kind::If => {
                    arity[i] = end_arity(code, &ins[i])?;
                    stack.push(i);
                }
                Kind::Else => {
                    let o = *stack.last()?;
                    if ins[o].kind != Kind::If || else_of[o] != NONE {
                        return None;
                    }
                    else_of[o] = i;
                    opener_of[i] = o;
                }
                Kind::End => {
                    let o = stack.pop()?;
                    end_of[o] = i;
                    opener_of[i] = o;
                }
                Kind::BrTable => {
                    table_of[i] = t;
                    t += 1;
                }
                _ => {}
            }
        }
        if !stack.is_empty() || t != tables.len() {
            return None;
        }
    }
    let relocated = {
        let mut r = vec![false; n];
        for x in &body.relocs {
            let at = x.offset as usize;
            let k = ins.partition_point(|y| y.start <= at).checked_sub(1)?;
            if at >= ins[k].end {
                return None;
            }
            r[k] = true;
        }
        r
    };
    // The target opener of a branch at `i` to depth `d` (`NONE`: the
    // function), or `None` past the function.
    let target = |i: usize, d: u32| -> Option<usize> {
        let mut o = parent[i];
        for _ in 0..d {
            if o == NONE {
                return None;
            }
            o = parent[o];
        }
        Some(o)
    };

    // Heights before every live instruction, every opener's frame height,
    // and the dead instructions.
    let mut height_at = vec![0usize; n];
    let mut frame_h = vec![0usize; n];
    let mut dead = vec![false; n];
    {
        let mut frames = vec![Frame {
            opener: NONE,
            height: 0,
            results,
            unreachable: false,
            dead: false,
            named: false,
            then_falls: false,
            keep_filler: false,
        }];
        let mut h = 0usize;
        for i in 0..n {
            let f = frames.last()?;
            let (fdead, fun, fh, fres) = (f.dead, f.unreachable, f.height, f.results);
            height_at[i] = h;
            match ins[i].kind {
                Kind::Block | Kind::Loop | Kind::If => {
                    if fdead || fun {
                        if !fdead && frames.last()?.keep_filler {
                            return None;
                        }
                        dead[i] = true;
                        frames.push(Frame {
                            opener: i,
                            height: 0,
                            results: 0,
                            unreachable: true,
                            dead: true,
                            named: false,
                            then_falls: false,
                            keep_filler: false,
                        });
                        continue;
                    }
                    if ins[i].kind == Kind::If {
                        if h < fh + 1 {
                            return None;
                        }
                        h -= 1;
                    }
                    frame_h[i] = h;
                    frames.push(Frame {
                        opener: i,
                        height: h,
                        results: arity[i],
                        unreachable: false,
                        dead: false,
                        named: false,
                        then_falls: false,
                        keep_filler: false,
                    });
                }
                Kind::Else => {
                    if fdead {
                        dead[i] = true;
                        continue;
                    }
                    if (!fun && h != fh + fres) || frames.last()?.keep_filler {
                        return None;
                    }
                    h = fh;
                    let f = frames.last_mut()?;
                    f.then_falls = !fun;
                    f.unreachable = false;
                    f.keep_filler = false;
                }
                Kind::End => {
                    let f = frames.pop()?;
                    if f.dead {
                        dead[i] = true;
                        continue;
                    }
                    if (!f.unreachable && h != f.height + f.results) || f.keep_filler {
                        return None;
                    }
                    // An `if` with a result and no `else` does not validate.
                    if ins[f.opener].kind == Kind::If && f.results != 0 && else_of[f.opener] == NONE
                    {
                        return None;
                    }
                    h = f.height + f.results;
                    // Whether any path leaves the construct: falling through
                    // its `end`, the zero path of an `if` without `else` or a
                    // `then` arm that falls through, or a branch to its label
                    // (a `loop`'s label re-enters it).
                    let leaves = !f.unreachable
                        || (ins[f.opener].kind == Kind::If
                            && (else_of[f.opener] == NONE || f.then_falls))
                        || (ins[f.opener].kind != Kind::Loop && f.named);
                    let outer = frames.last_mut()?;
                    if !leaves {
                        outer.unreachable = true;
                        outer.keep_filler = h != outer.height + outer.results
                            || (outer.opener == NONE && outer.results != 0);
                    }
                }
                Kind::Unreachable if fun && !fdead && frames.last()?.keep_filler => {
                    // The filler a construct no path leaves needs (Frame).
                    frames.last_mut()?.keep_filler = false;
                }
                _ if fdead || fun => {
                    if frames.last()?.keep_filler {
                        return None;
                    }
                    dead[i] = true;
                }
                Kind::Br(_) | Kind::Return | Kind::Unreachable => {
                    if let Kind::Br(d) = ins[i].kind {
                        name(&mut frames, d)?;
                    }
                    frames.last_mut()?.unreachable = true;
                }
                Kind::BrTable => {
                    if h < fh + 1 {
                        return None;
                    }
                    h -= 1;
                    height_at[i] = h;
                    for &d in &tables[table_of[i]] {
                        name(&mut frames, d)?;
                    }
                    frames.last_mut()?.unreachable = true;
                }
                Kind::BrIf(d) => {
                    if h < fh + 1 {
                        return None;
                    }
                    h -= 1;
                    name(&mut frames, d)?;
                }
                Kind::Plain | Kind::Get(_) | Kind::Set(_) | Kind::Tee(_) => {
                    let (pops, pushes) = effect(code, &ins[i], types)?;
                    if h < fh + pops {
                        return None;
                    }
                    h = h - pops + pushes;
                }
            }
        }
        let f = frames.pop()?;
        if !frames.is_empty() || (!f.unreachable && h != results) || f.keep_filler {
            return None;
        }
    }

    let mut del = dead.clone();
    let mut stats = ControlStats {
        dead: dead.iter().filter(|&&d| d).count(),
        ..ControlStats::default()
    };

    // 2. Branches whose target falling through reaches.
    for i in 0..n {
        if del[i] {
            continue;
        }
        let t = match ins[i].kind {
            Kind::Br(d) => target(i, d)?,
            Kind::Return => NONE,
            _ => continue,
        };
        if t != NONE && ins[t].kind == Kind::Loop {
            continue;
        }
        let cur = height_at[i];
        let need = if t == NONE {
            results
        } else {
            frame_h[t] + arity[t]
        };
        if cur != need {
            continue;
        }
        let mut j = i + 1;
        let reaches = loop {
            if j == n {
                break t == NONE;
            }
            if del[j] || (ins[j].kind == Kind::Plain && code[ins[j].start] == 0x01) {
                j += 1;
                continue;
            }
            match ins[j].kind {
                Kind::End => {
                    let o = opener_of[j];
                    if o == t {
                        break true;
                    }
                    if cur != frame_h[o] + arity[o] {
                        break false;
                    }
                    j += 1;
                }
                Kind::Else => {
                    let o = opener_of[j];
                    if cur != frame_h[o] + arity[o] {
                        break false;
                    }
                    if o == t {
                        break true;
                    }
                    j = end_of[o] + 1;
                }
                _ => break false,
            }
        };
        if reaches {
            del[i] = true;
            if ins[i].kind == Kind::Return {
                stats.returns += 1;
            } else {
                stats.branches += 1;
            }
        }
    }

    // The labels the remaining branches name.
    let mut named = vec![false; n];
    for i in 0..n {
        if del[i] {
            continue;
        }
        let depths: Vec<u32> = match ins[i].kind {
            Kind::Br(d) | Kind::BrIf(d) => vec![d],
            Kind::BrTable => tables[table_of[i]].clone(),
            _ => continue,
        };
        for d in depths {
            let o = target(i, d)?;
            if o != NONE {
                named[o] = true;
            }
        }
    }

    // 3. Unnamed blocks and loops.
    for o in 0..n {
        if !del[o] && matches!(ins[o].kind, Kind::Block | Kind::Loop) && !named[o] {
            del[o] = true;
            del[end_of[o]] = true;
            stats.blocks += 1;
        }
    }

    // 4. Empty `else` arms.
    for o in 0..n {
        if del[o] || ins[o].kind != Kind::If || arity[o] != 0 {
            continue;
        }
        let e = else_of[o];
        if e != NONE && !del[e] && (e + 1..end_of[o]).all(|k| del[k]) {
            del[e] = true;
            stats.elses += 1;
        }
    }

    // 5. `if; br d; end` with d >= 1 as `br_if (d - 1)`.
    let mut to_br_if = vec![false; n];
    for o in 0..n {
        if del[o] || ins[o].kind != Kind::If || arity[o] != 0 || named[o] {
            continue;
        }
        let e = else_of[o];
        if e != NONE && !del[e] {
            continue;
        }
        let arm_end = if e != NONE { e } else { end_of[o] };
        let live: Vec<usize> = (o + 1..arm_end).filter(|&k| !del[k]).collect();
        let [b] = live[..] else { continue };
        if let Kind::Br(d) = ins[b].kind
            && d >= 1
            && height_at[b] == frame_h[o]
        {
            del[o] = true;
            del[end_of[o]] = true;
            to_br_if[b] = true;
            stats.br_ifs += 1;
        }
    }

    if stats == ControlStats::default() {
        return Some(None);
    }
    for (k, &r) in relocated.iter().enumerate() {
        if r && del[k] {
            return None;
        }
    }

    // Re-encode: every kept branch's depth counts the kept constructs
    // between it and its target.
    let new_depth = |i: usize, d: u32| -> Option<u32> {
        let mut o = parent[i];
        let mut k = 0u32;
        for _ in 0..d {
            if o == NONE {
                return None;
            }
            if !del[o] {
                k += 1;
            }
            o = parent[o];
        }
        if o != NONE && del[o] {
            return None;
        }
        Some(k)
    };
    let mut out = Vec::with_capacity(code.len());
    let mut new_start = vec![NONE; n];
    for i in 0..n {
        if del[i] {
            continue;
        }
        new_start[i] = out.len();
        let x = &ins[i];
        match x.kind {
            Kind::Br(d) | Kind::BrIf(d) => {
                let op = if to_br_if[i] || x.kind == Kind::BrIf(d) {
                    0x0d
                } else {
                    0x0c
                };
                out.push(op);
                write_uleb128(&mut out, u64::from(new_depth(i, d)?));
            }
            Kind::BrTable => {
                let depths = &tables[table_of[i]];
                out.push(0x0e);
                write_uleb128(&mut out, depths.len() as u64 - 1);
                for &d in depths {
                    write_uleb128(&mut out, u64::from(new_depth(i, d)?));
                }
            }
            _ => out.extend_from_slice(&code[x.start..x.end]),
        }
    }
    let mut relocs = Vec::with_capacity(body.relocs.len());
    for r in &body.relocs {
        let at = r.offset as usize;
        let k = ins.partition_point(|y| y.start <= at).checked_sub(1)?;
        let offset = u32::try_from(at - ins[k].start + new_start[k]).ok()?;
        relocs.push(Reloc { offset, ..*r });
    }
    Some(Some((
        Body {
            declared: body.declared.clone(),
            code: out,
            relocs,
        },
        stats,
    )))
}

#[cfg(test)]
mod tests {
    use trust_cg_verify::wasm_cfg_proofs::{FuncSig, ValKind};
    use trust_cg_verify::wasm_local_tv::{ControlTvRequest, TvBody, validate_control};

    use super::super::super::encode::{RelocKind, RelocTarget, ValType};
    use super::*;

    const UNREACHABLE: u8 = 0x00;
    const BLOCK: u8 = 0x02;
    const LOOP: u8 = 0x03;
    const IF: u8 = 0x04;
    const ELSE: u8 = 0x05;
    const END: u8 = 0x0b;
    const BR: u8 = 0x0c;
    const BR_IF: u8 = 0x0d;
    const RETURN: u8 = 0x0f;
    const CALL: u8 = 0x10;
    const GET: u8 = 0x20;
    const SET: u8 = 0x21;
    const I32_CONST: u8 = 0x41;
    const VOID: u8 = 0x40;

    /// Function 0 is `(i32) -> (i32)`.
    struct Types;

    impl TvTypes for Types {
        fn func(&self, index: u32) -> Option<FuncSig> {
            (index == 0).then(|| FuncSig {
                params: vec![ValKind::I32],
                results: vec![ValKind::I32],
            })
        }
        fn type_at(&self, _: u32) -> Option<FuncSig> {
            None
        }
        fn global(&self, _: u32) -> Option<ValKind> {
            None
        }
    }

    fn body(code: &[u8]) -> Body {
        Body {
            declared: vec![ValType::I32],
            code: code.to_vec(),
            relocs: Vec::new(),
        }
    }

    /// Clean `code` (one `i32` parameter, one declared `i32`, `results`
    /// results), check the result with the control validator, and return it.
    #[track_caller]
    fn clean(results: usize, code: &[u8]) -> (Vec<u8>, ControlStats) {
        let pre = body(code);
        let (post, stats) = cleanup(results, &pre, &Types).expect("cleaned");
        let locals = [ValKind::I32];
        validate_control(&ControlTvRequest {
            results,
            pre: TvBody {
                locals: &locals,
                code: &pre.code,
                relocs: &[],
            },
            post: TvBody {
                locals: &locals,
                code: &post.code,
                relocs: &[],
            },
            types: &Types,
            max_work: 1 << 20,
        })
        .unwrap_or_else(|f| panic!("the validator refused the cleanup: {f}"));
        (post.code, stats)
    }

    #[test]
    fn relooper_arms_lose_their_branches_and_blocks() {
        // block; if p0 { l1 = 1; br 1 } else { l1 = 2; br 1 }; end; l1; return
        let code = [
            BLOCK,
            VOID,
            GET,
            0,
            IF,
            VOID,
            I32_CONST,
            1,
            SET,
            1,
            BR,
            1,
            ELSE,
            I32_CONST,
            2,
            SET,
            1,
            BR,
            1,
            END,
            END,
            GET,
            1,
            RETURN,
            UNREACHABLE,
        ];
        let (post, stats) = clean(1, &code);
        assert_eq!(
            post,
            [
                GET, 0, IF, VOID, I32_CONST, 1, SET, 1, ELSE, I32_CONST, 2, SET, 1, END, GET, 1
            ]
        );
        assert_eq!(stats.branches, 2);
        assert_eq!(stats.returns, 1);
        assert_eq!(stats.dead, 1);
        assert_eq!(stats.blocks, 1);
    }

    #[test]
    fn a_one_branch_arm_becomes_br_if_and_an_empty_else_goes() {
        // block; p0; if; br 1; end; l1 = 6; end; l1
        let (post, stats) = clean(
            1,
            &[
                BLOCK, VOID, GET, 0, IF, VOID, BR, 1, END, I32_CONST, 6, SET, 1, END, GET, 1,
            ],
        );
        assert_eq!(
            post,
            [
                BLOCK, VOID, GET, 0, BR_IF, 0, I32_CONST, 6, SET, 1, END, GET, 1
            ]
        );
        assert_eq!(stats.br_ifs, 1);
        // p0; if; l1 = 3; else; end; l1
        let (post, stats) = clean(
            1,
            &[GET, 0, IF, VOID, I32_CONST, 3, SET, 1, ELSE, END, GET, 1],
        );
        assert_eq!(post, [GET, 0, IF, VOID, I32_CONST, 3, SET, 1, END, GET, 1]);
        assert_eq!(stats.elses, 1);
    }

    #[test]
    fn code_after_a_construct_no_path_leaves_is_dead_and_keeps_its_filler() {
        // block; loop; p0; br_if 1; br 0; end; l1 = 1; end; 9: the store after
        // the loop never runs; the loop is entered at the block's height, so
        // no filler is needed.
        let (post, stats) = clean(
            1,
            &[
                BLOCK, VOID, LOOP, VOID, GET, 0, BR_IF, 1, BR, 0, END, I32_CONST, 1, SET, 1, END,
                I32_CONST, 9,
            ],
        );
        assert_eq!(
            post,
            [
                BLOCK, VOID, LOOP, VOID, GET, 0, BR_IF, 1, BR, 0, END, END, I32_CONST, 9
            ]
        );
        assert_eq!(stats.dead, 2);
        // A function with a result ending with such a loop keeps the
        // `unreachable` after it and loses what follows.
        let (post, _) = clean(
            1,
            &[
                LOOP,
                VOID,
                GET,
                0,
                SET,
                1,
                BR,
                0,
                END,
                UNREACHABLE,
                I32_CONST,
                1,
                RETURN,
            ],
        );
        assert_eq!(post, [LOOP, VOID, GET, 0, SET, 1, BR, 0, END, UNREACHABLE]);
    }

    #[test]
    fn a_branch_that_discards_values_or_targets_a_loop_is_kept() {
        // block; 5; br 0; end; p0: the branch drops the 5.
        let pre = body(&[BLOCK, VOID, I32_CONST, 5, BR, 0, END, GET, 0]);
        assert!(cleanup(1, &pre, &Types).is_none());
        // loop; p0; br_if 1 ... `br 0` at the end of a loop re-enters it.
        let pre = body(&[
            BLOCK, VOID, LOOP, VOID, GET, 0, BR_IF, 1, BR, 0, END, END, GET, 0,
        ]);
        assert!(cleanup(1, &pre, &Types).is_none());
    }

    #[test]
    fn bodies_it_cannot_account_for_are_left_alone() {
        // A typed block.
        let pre = body(&[BLOCK, 0x7f, GET, 0, END, RETURN]);
        assert!(cleanup(1, &pre, &Types).is_none());
        // A call to a function with no signature.
        let pre = body(&[GET, 0, CALL, 5, RETURN]);
        assert!(cleanup(1, &pre, &Types).is_none());
        // A dead instruction that carries a relocation.
        let mut pre = body(&[GET, 0, RETURN, GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00]);
        pre.relocs.push(Reloc {
            offset: 6,
            kind: RelocKind::FunctionIndexLeb,
            target: RelocTarget::Func(0),
            addend: 0,
        });
        assert!(cleanup(1, &pre, &Types).is_none());
    }

    #[test]
    fn relocations_move_with_their_instruction() {
        // block; br 0; end; p0; call 0 (relocated); return
        let mut pre = body(&[
            BLOCK, VOID, BR, 0, END, GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00, RETURN,
        ]);
        pre.relocs.push(Reloc {
            offset: 8,
            kind: RelocKind::FunctionIndexLeb,
            target: RelocTarget::Func(0),
            addend: 0,
        });
        let (post, _) = cleanup(1, &pre, &Types).expect("cleaned");
        assert_eq!(post.code, [GET, 0, CALL, 0x80, 0x80, 0x80, 0x80, 0x00]);
        assert_eq!(post.relocs.len(), 1);
        assert_eq!(post.relocs[0].offset, 3);
    }
}
