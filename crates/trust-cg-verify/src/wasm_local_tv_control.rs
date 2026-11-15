// trust-cg-verify/wasm_local_tv_control.rs - validation of wasm control cleanup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Translation validation of the CONTROL cleanup of the wasm32 lane's local
//! emission pass (`trust-cg-codegen` `wasm/opt/control.rs`): branches and
//! `return`s whose target is reached by falling through, code after an
//! unconditional transfer, `block`s and `loop`s no branch names, empty
//! `else` arms, and `if` arms that are one `br` turned into `br_if`.
//!
//! [`validate_control`] is given two bodies of ONE function — PRE and POST —
//! with the same declared locals, decodes both with
//! [`crate::wasm_cfg_proofs::decode_body`], and accepts only when the two are
//! related by a LOCKSTEP SIMULATION that it builds itself, from the function
//! entry, over pairs of program points:
//!
//! - **Control moves.** Each side runs its own control instructions on its
//!   own: `nop`, a `block`/`loop` opener entered by falling through, an `end`
//!   or `else` reached by falling through (which must leave exactly the
//!   frame's height plus its results on the stack), and `br` (which keeps the
//!   label's values on top of the label's height and continues after the
//!   label's `end`, or at the `loop` it names). None of these computes
//!   anything: they only move the program point and truncate the stack.
//! - **Paired points.** Between moves each side stops at its next real
//!   instruction, and the two must agree:
//!   - two byte-identical non-control instructions with identical
//!     relocations, executed on the same stack, push the same values (a
//!     float operation whose NaN result is nondeterministic is evaluated
//!     once on each side, in the same order, so every post execution has a
//!     pre execution with the same choices);
//!   - two conditional branches (`if` or `br_if`, in either combination)
//!     pop the same condition, and the nonzero and zero successors are
//!     paired with each other;
//!   - two `br_table`s with tables of one length pair every entry and the
//!     default;
//!   - two returns (`return`, a `br` to the function's label, or falling off
//!     the end with exactly the results on the stack) return the same top
//!     values; two `unreachable`s both trap.
//!
//!   Anything else refuses the function.
//!
//! **Stacks.** A stack is a vector of value TOKENS: a real instruction pops
//! its operands and pushes fresh tokens, the same on both sides, so two
//! sides that reach a pair with equal token vectors hold equal values. The
//! check therefore compares the whole token vectors at every pair, not only
//! their heights: two sides whose control moves keep different values of an
//! equal-height stack are refused. Heights come from the validator's own
//! arity table and the function and type signatures the caller supplies; a
//! frame's height is recorded where it is entered and must be the same on
//! every path, and an instruction may not pop below its frame.
//!
//! **Why this is enough.** At the entry the two states are equal (same
//! parameters, the same declared locals, both zero, the same memory and
//! globals, empty stacks). Control moves change only the program point and
//! the stack; real instructions are identical and see equal stacks, locals,
//! memory and globals, so they make equal changes; conditional branches see
//! equal conditions and take paired successors. By induction over the
//! executed real instructions, every execution of POST performs the same
//! effects and returns the same values as an execution of PRE.
//!
//! **POST validates.** Every POST instruction other than `end` and `else`
//! must be reached by the simulation, so the emitted body has no code the
//! check did not see (WebAssembly validates unreachable code too), except an
//! `unreachable` directly after the unreached `end` of a construct in its
//! own frame: no path executes it (the simulation follows both successors
//! of every conditional, so it reaches every instruction an execution can),
//! it takes no operand, and it makes the stack polymorphic for the frame's
//! `end`. A reached
//! instruction pops nothing below its frame and sees the values of its PRE
//! twin, so it types as that twin does. An `end` or `else` the simulation
//! never reaches must follow an unconditional transfer of its own frame
//! (the stack is polymorphic there) or the unreached `end` of a construct
//! nested directly in it entered at the frame's own height (both frames
//! leave no values); the function's end, when no path falls off it, the
//! same, with no results. Only the empty block type is modelled: any other
//! block type, a relocation (on either side) on any instruction other than a
//! paired non-control one (a control instruction, `nop`, the filler, an
//! unreached `end`, code the simulation never pairs), a cycle of control
//! moves with no real instruction, and a state over the work budget refuse
//! the function.
//!
//! **What this does not claim.** Like [`super::validate`], this is an
//! emission-level equivalence of two bodies of one function given the
//! signatures the caller supplies; it says nothing about whether either
//! computes what the trust-ir function computes.

use std::collections::HashMap;

use super::{TvBody, TvFailure, TvFailureKind, TvReloc, TvTypes, fail};
use crate::wasm_cfg_proofs::{BlockType, DecodedInst, Imm, decode_body};

/// One control-cleanup validation request.
pub struct ControlTvRequest<'a> {
    /// The function's result count.
    pub results: usize,
    /// The body before the cleanup.
    pub pre: TvBody<'a>,
    /// The cleaned body; its declared locals must equal `pre`'s.
    pub post: TvBody<'a>,
    /// Signatures for `call` / `call_indirect`.
    pub types: &'a dyn TvTypes,
    /// Work budget (control moves and paired points).
    pub max_work: usize,
}

/// What an accepted control-cleanup validation checked.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ControlTvReport {
    /// Pairs of program points the simulation visited.
    pub states: usize,
    /// Real instructions paired.
    pub paired: usize,
}

const NONE: usize = usize::MAX;

/// One decoded body with its structure.
struct Side<'a> {
    ins: Vec<DecodedInst>,
    code: &'a [u8],
    /// Relocations of every instruction, relative to its start.
    relocs: Vec<Vec<(u32, u8, u64, i32)>>,
    /// The matching `end` of every opener and of every `else`.
    end_of: Vec<usize>,
    /// The `else` of every `if` that has one.
    else_of: Vec<usize>,
    /// The opener of every `end` and `else`.
    opener_of: Vec<usize>,
    /// The innermost opener enclosing every instruction (`NONE`: the
    /// function frame).
    parent: Vec<usize>,
    /// The height recorded at every opener (after an `if` pops its
    /// condition).
    height: Vec<Option<usize>>,
    /// Instructions the simulation reached.
    reached: Vec<bool>,
    /// Instructions whose relocations were compared with a twin's in a
    /// paired non-control instruction.
    relocs_paired: Vec<bool>,
    /// Whether some path fell off the function's end.
    fell_off: bool,
}

fn decode_side<'a>(body: &TvBody<'a>, which: &str) -> Result<Side<'a>, TvFailure> {
    let ins = decode_body(body.code, 0).map_err(|e| {
        fail(
            TvFailureKind::Undecodable,
            None,
            format!("{which} body: {e:?}"),
        )
    })?;
    let n = ins.len();
    let mut relocs: Vec<Vec<(u32, u8, u64, i32)>> = vec![Vec::new(); n];
    for r in body.relocs {
        let at = r.offset as usize;
        let k = ins
            .partition_point(|x| x.offset <= at)
            .checked_sub(1)
            .filter(|&k| at < ins[k].offset + ins[k].size)
            .ok_or_else(|| {
                fail(
                    TvFailureKind::RelocUnsupported,
                    None,
                    format!("{which} relocation at {at} is outside every instruction"),
                )
            })?;
        let TvReloc {
            kind,
            target,
            addend,
            ..
        } = *r;
        relocs[k].push(((at - ins[k].offset) as u32, kind, target, addend));
    }
    for v in &mut relocs {
        v.sort_unstable();
    }
    let mut end_of = vec![NONE; n];
    let mut else_of = vec![NONE; n];
    let mut opener_of = vec![NONE; n];
    let mut parent = vec![NONE; n];
    let mut stack: Vec<usize> = Vec::new();
    let unbalanced = || {
        fail(
            TvFailureKind::Undecodable,
            None,
            format!("{which} body has unbalanced structure"),
        )
    };
    for i in 0..n {
        parent[i] = stack.last().copied().unwrap_or(NONE);
        match ins[i].opcode {
            0x02..=0x04 => {
                match ins[i].imm {
                    Imm::Block(BlockType::Empty) => {}
                    Imm::Block(_) => {
                        return Err(fail(
                            TvFailureKind::Unsupported,
                            None,
                            format!("{which} body has a block type with results"),
                        ));
                    }
                    _ => return Err(unbalanced()),
                }
                stack.push(i);
            }
            0x05 => {
                let o = *stack.last().ok_or_else(unbalanced)?;
                if ins[o].opcode != 0x04 || else_of[o] != NONE {
                    return Err(unbalanced());
                }
                else_of[o] = i;
                opener_of[i] = o;
                // The `else` itself belongs to the `if` frame.
            }
            0x0b => {
                let o = stack.pop().ok_or_else(unbalanced)?;
                end_of[o] = i;
                opener_of[i] = o;
                if else_of[o] != NONE {
                    end_of[else_of[o]] = i;
                }
            }
            _ => {}
        }
    }
    if !stack.is_empty() {
        return Err(unbalanced());
    }
    Ok(Side {
        ins,
        code: body.code,
        relocs,
        end_of,
        else_of,
        opener_of,
        parent,
        height: vec![None; n],
        reached: vec![false; n],
        relocs_paired: vec![false; n],
        fell_off: false,
    })
}

/// Operands popped and results pushed by a non-control instruction; `None`
/// for one this model has no rule for.
fn stack_effect(x: &DecodedInst, types: &dyn TvTypes) -> Option<(usize, usize)> {
    Some(match x.opcode {
        0x01 => (0, 0),
        0x1a => (1, 0),
        0x1b => (3, 1),
        0x10 => {
            let Imm::Index(f) = x.imm else { return None };
            let sig = types.func(f)?;
            (sig.params.len(), sig.results.len())
        }
        0x11 => {
            let Imm::CallIndirect { type_idx, .. } = x.imm else {
                return None;
            };
            let sig = types.type_at(type_idx)?;
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
        0xfc => match x.sub? {
            0..=7 => (1, 1),
            10 | 11 => (3, 0),
            _ => return None,
        },
        _ => return None,
    })
}

/// Where a side stopped.
enum Point {
    /// A real instruction (non-control, `if`, `br_if`, `br_table`,
    /// `unreachable`) at this index, on this stack.
    Real(usize, Vec<u32>),
    /// The function returns these values.
    Return(Vec<u32>),
}

struct Walk<'r> {
    results: usize,
    types: &'r dyn TvTypes,
    work: usize,
    max_work: usize,
    next_token: u32,
}

impl Walk<'_> {
    fn spend(&mut self) -> Result<(), TvFailure> {
        self.work += 1;
        if self.work > self.max_work {
            Err(fail(
                TvFailureKind::Budget,
                None,
                "control simulation budget",
            ))
        } else {
            Ok(())
        }
    }

    fn token(&mut self) -> u32 {
        self.next_token = self.next_token.wrapping_add(1);
        self.next_token
    }
}

fn mismatch(detail: impl Into<String>) -> TvFailure {
    fail(TvFailureKind::StructureMismatch, None, detail)
}

/// Record (or check) the height of opener `o`.
fn enter(side: &mut Side<'_>, o: usize, h: usize) -> Result<(), TvFailure> {
    match side.height[o] {
        None => {
            side.height[o] = Some(h);
            Ok(())
        }
        Some(k) if k == h => Ok(()),
        Some(k) => Err(fail(
            TvFailureKind::StackMismatch,
            None,
            format!("frame at {o} entered at heights {k} and {h}"),
        )),
    }
}

fn frame_height(side: &Side<'_>, o: usize) -> Result<usize, TvFailure> {
    side.height[o].ok_or_else(|| {
        fail(
            TvFailureKind::StackMismatch,
            None,
            format!("frame at {o} used before it was entered"),
        )
    })
}

/// The height below which an instruction at `pc` may not pop.
fn floor(side: &Side<'_>, pc: usize) -> Result<usize, TvFailure> {
    match side.parent[pc] {
        NONE => Ok(0),
        o => frame_height(side, o),
    }
}

/// Where a branch goes: the program point and stack after it, or (`Some`) the
/// values the function returns.
type Succ = (usize, Option<Vec<u32>>, Vec<u32>);

/// Take a branch from `pc` to label `depth` with `stack`: the program point
/// and stack after it, or the function's return.
fn branch(
    side: &Side<'_>,
    walk: &Walk<'_>,
    pc: usize,
    depth: u32,
    mut stack: Vec<u32>,
) -> Result<Succ, TvFailure> {
    let mut o = side.parent[pc];
    for _ in 0..depth {
        if o == NONE {
            return Err(mismatch(format!(
                "branch at {pc} names a label past the function"
            )));
        }
        o = side.parent[o];
    }
    if o == NONE {
        if stack.len() < walk.results {
            return Err(fail(
                TvFailureKind::StackMismatch,
                None,
                "return below its results",
            ));
        }
        let ret = stack.split_off(stack.len() - walk.results);
        return Ok((NONE, Some(ret), Vec::new()));
    }
    // Every label is of the empty block type: it carries no value.
    let h = frame_height(side, o)?;
    if stack.len() < h {
        return Err(fail(
            TvFailureKind::StackMismatch,
            None,
            format!("branch at {pc} below its label's height"),
        ));
    }
    stack.truncate(h);
    let to = if side.ins[o].opcode == 0x03 {
        o + 1
    } else {
        side.end_of[o] + 1
    };
    Ok((to, None, stack))
}

/// Run `side`'s control moves from `pc` until its next real instruction or
/// its return.
fn advance(
    side: &mut Side<'_>,
    walk: &mut Walk<'_>,
    mut pc: usize,
    mut stack: Vec<u32>,
) -> Result<Point, TvFailure> {
    let n = side.ins.len();
    let mut moves = 0usize;
    loop {
        walk.spend()?;
        moves += 1;
        if moves > n + 2 {
            return Err(mismatch(
                "a cycle of control moves with no real instruction",
            ));
        }
        if pc == n {
            if stack.len() != walk.results {
                return Err(fail(
                    TvFailureKind::StackMismatch,
                    None,
                    "falls off the function end with another height than its results",
                ));
            }
            side.fell_off = true;
            return Ok(Point::Return(stack));
        }
        side.reached[pc] = true;
        let x = &side.ins[pc];
        match x.opcode {
            0x01 => pc += 1,
            0x02 | 0x03 => {
                enter(side, pc, stack.len())?;
                pc += 1;
            }
            0x0b | 0x05 => {
                let o = side.opener_of[pc];
                if stack.len() != frame_height(side, o)? {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        format!("falls through {pc} with another height than its frame's"),
                    ));
                }
                // Falling off a `then` arm continues after the `if`'s `end`;
                // falling through an `end` continues after it.
                pc = if x.opcode == 0x05 {
                    side.end_of[pc] + 1
                } else {
                    pc + 1
                };
            }
            0x0c => {
                let Imm::Depth(d) = x.imm else {
                    return Err(mismatch("br without a depth"));
                };
                let (to, ret, s) = branch(side, walk, pc, d, stack)?;
                if let Some(ret) = ret {
                    return Ok(Point::Return(ret));
                }
                pc = to;
                stack = s;
            }
            0x0f => {
                if stack.len() < walk.results {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        "return below its results",
                    ));
                }
                let ret = stack.split_off(stack.len() - walk.results);
                return Ok(Point::Return(ret));
            }
            _ => return Ok(Point::Real(pc, stack)),
        }
    }
}

/// The two successors of a conditional branch at `pc` (the condition already
/// popped from `stack`): (nonzero, zero).
fn conditional(
    side: &mut Side<'_>,
    walk: &Walk<'_>,
    pc: usize,
    stack: Vec<u32>,
) -> Result<(Succ, Succ), TvFailure> {
    let x = &side.ins[pc];
    match x.opcode {
        0x04 => {
            enter(side, pc, stack.len())?;
            let zero = match side.else_of[pc] {
                NONE => side.end_of[pc] + 1,
                e => e + 1,
            };
            Ok(((pc + 1, None, stack.clone()), (zero, None, stack)))
        }
        0x0d => {
            let Imm::Depth(d) = x.imm else {
                return Err(mismatch("br_if without a depth"));
            };
            let taken = branch(side, walk, pc, d, stack.clone())?;
            Ok((taken, (pc + 1, None, stack)))
        }
        _ => Err(mismatch(format!(
            "instruction at {pc} is not a conditional branch"
        ))),
    }
}

/// Validate a control cleanup (module docs).
pub fn validate_control(req: &ControlTvRequest<'_>) -> Result<ControlTvReport, TvFailure> {
    if req.pre.locals != req.post.locals {
        return Err(mismatch("the cleanup changed the declared locals"));
    }
    let mut pre = decode_side(&req.pre, "pre")?;
    let mut post = decode_side(&req.post, "post")?;
    let mut walk = Walk {
        results: req.results,
        types: req.types,
        work: 0,
        max_work: req.max_work,
        next_token: 0,
    };
    let mut report = ControlTvReport::default();
    // Pairs of program points, with the height they were first reached at.
    let mut seen: HashMap<(usize, usize), usize> = HashMap::new();
    let start_a = advance(&mut pre, &mut walk, 0, Vec::new())?;
    let start_b = advance(&mut post, &mut walk, 0, Vec::new())?;
    let mut work: Vec<(Point, Point)> = vec![(start_a, start_b)];
    while let Some((a, b)) = work.pop() {
        walk.spend()?;
        let (pa, sa, pb, sb) = match (a, b) {
            (Point::Return(x), Point::Return(y)) => {
                if x != y {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        "the two sides return different values",
                    ));
                }
                continue;
            }
            (Point::Real(pa, sa), Point::Real(pb, sb)) => (pa, sa, pb, sb),
            _ => return Err(mismatch("one side returns where the other does not")),
        };
        if sa != sb {
            return Err(fail(
                TvFailureKind::StackMismatch,
                None,
                format!("stacks differ at pre {pa} / post {pb}"),
            ));
        }
        match seen.get(&(pa, pb)) {
            Some(&h) if h == sa.len() => continue,
            Some(_) => {
                return Err(fail(
                    TvFailureKind::StackMismatch,
                    None,
                    format!("pre {pa} / post {pb} reached at two heights"),
                ));
            }
            None => {
                // Token names are local to a path: a pair reached again with
                // the same height holds equal stacks on both sides by the
                // same induction, whatever the names.
                seen.insert((pa, pb), sa.len());
            }
        }
        report.states += 1;
        let xa = pre.ins[pa].clone();
        let xb = post.ins[pb].clone();
        let mut stack = sa;
        match (xa.opcode, xb.opcode) {
            (0x00, 0x00) => {}
            (0x04 | 0x0d, 0x04 | 0x0d) => {
                if stack.len() <= floor(&pre, pa)? || stack.len() <= floor(&post, pb)? {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        "condition below its frame",
                    ));
                }
                stack.pop();
                let (an, az) = conditional(&mut pre, &walk, pa, stack.clone())?;
                let (bn, bz) = conditional(&mut post, &walk, pb, stack)?;
                for (x, y) in [(an, bn), (az, bz)] {
                    let p = resume(&mut pre, &mut walk, x)?;
                    let q = resume(&mut post, &mut walk, y)?;
                    work.push((p, q));
                }
            }
            (0x0e, 0x0e) => {
                let (
                    Imm::Table {
                        targets: ta,
                        default: da,
                    },
                    Imm::Table {
                        targets: tb,
                        default: db,
                    },
                ) = (&xa.imm, &xb.imm)
                else {
                    return Err(mismatch("br_table without a table"));
                };
                if ta.len() != tb.len() {
                    return Err(mismatch(format!(
                        "br_table at pre {pa} and post {pb} differ in length"
                    )));
                }
                if stack.len() <= floor(&pre, pa)? || stack.len() <= floor(&post, pb)? {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        "index below its frame",
                    ));
                }
                stack.pop();
                let pairs: Vec<(u32, u32)> = ta
                    .iter()
                    .copied()
                    .zip(tb.iter().copied())
                    .chain([(*da, *db)])
                    .collect();
                for (x, y) in pairs {
                    let p = branch(&pre, &walk, pa, x, stack.clone())?;
                    let q = branch(&post, &walk, pb, y, stack.clone())?;
                    let p = resume(&mut pre, &mut walk, p)?;
                    let q = resume(&mut post, &mut walk, q)?;
                    work.push((p, q));
                }
            }
            (a, b) if is_control(a) || is_control(b) => {
                return Err(mismatch(format!(
                    "pre {pa} (0x{a:02x}) and post {pb} (0x{b:02x}) are not the same control"
                )));
            }
            _ => {
                let ba = &pre.code[xa.offset..xa.offset + xa.size];
                let bb = &post.code[xb.offset..xb.offset + xb.size];
                if ba != bb {
                    return Err(fail(
                        TvFailureKind::EffectMismatch,
                        None,
                        format!("pre {pa} and post {pb} are different instructions"),
                    ));
                }
                if pre.relocs[pa] != post.relocs[pb] {
                    return Err(fail(
                        TvFailureKind::RelocUnsupported,
                        None,
                        format!("pre {pa} and post {pb} carry different relocations"),
                    ));
                }
                pre.relocs_paired[pa] = true;
                post.relocs_paired[pb] = true;
                let (pops, pushes) = stack_effect(&xa, walk.types).ok_or_else(|| {
                    fail(
                        TvFailureKind::Unsupported,
                        None,
                        format!("no stack rule for opcode 0x{:02x}", xa.opcode),
                    )
                })?;
                if stack.len() < pops + floor(&pre, pa)? || stack.len() < pops + floor(&post, pb)? {
                    return Err(fail(
                        TvFailureKind::StackMismatch,
                        None,
                        "pops below its frame",
                    ));
                }
                stack.truncate(stack.len() - pops);
                for _ in 0..pushes {
                    let t = walk.token();
                    stack.push(t);
                }
                report.paired += 1;
                let p = advance(&mut pre, &mut walk, pa + 1, stack.clone())?;
                let q = advance(&mut post, &mut walk, pb + 1, stack)?;
                work.push((p, q));
            }
        }
    }
    // Every relocation, on either side, must sit on a non-control
    // instruction the simulation paired with a twin carrying the same
    // relocations. The linker rewrites a relocated field, so one on a
    // control instruction (a depth, a block type) or on code the simulation
    // never paired would change bytes the check did not compare.
    for (which, side) in [("pre", &pre), ("post", &post)] {
        if let Some(i) =
            (0..side.ins.len()).find(|&i| !side.relocs[i].is_empty() && !side.relocs_paired[i])
        {
            return Err(fail(
                TvFailureKind::RelocUnsupported,
                None,
                format!(
                    "{which} instruction {i} (0x{:02x}) carries a relocation outside a paired \
                     non-control instruction",
                    side.ins[i].opcode
                ),
            ));
        }
    }
    for (i, x) in post.ins.iter().enumerate() {
        // An `unreachable` right after the unreached `end` of a construct
        // in its own frame executes nothing and needs no operand: it only
        // makes the stack polymorphic for the frame's `end` (module docs).
        let filler = x.opcode == 0x00
            && i > 0
            && post.ins[i - 1].opcode == 0x0b
            && !post.reached[i - 1]
            && post.parent[post.opener_of[i - 1]] == post.parent[i];
        if !post.reached[i] && !filler && !matches!(x.opcode, 0x05 | 0x0b) {
            return Err(mismatch(format!(
                "post instruction {i} (0x{:02x}) is never reached by the simulation",
                x.opcode
            )));
        }
    }
    // Unreached `end`s and `else`s, and the function's end when no path
    // falls off it, must validate on their own (module docs).
    let n = post.ins.len();
    for e in 0..=n {
        let frame = if e == n {
            if post.fell_off {
                continue;
            }
            // No path falls off the end: with results, only a transfer of
            // the function's own frame may precede it.
            if walk.results != 0 {
                if n > 0 && is_transfer(post.ins[n - 1].opcode) && post.parent[n - 1] == NONE {
                    continue;
                }
                return Err(mismatch(
                    "the function's end is never reached and has results",
                ));
            }
            NONE
        } else {
            if post.reached[e] || !matches!(post.ins[e].opcode, 0x05 | 0x0b) {
                continue;
            }
            post.opener_of[e]
        };
        if e == 0 {
            return Err(mismatch("an unreached end opens the body"));
        }
        let prev = e - 1;
        let px = &post.ins[prev];
        let ok = if is_transfer(px.opcode) {
            post.parent[prev] == frame
        } else if px.opcode == 0x0b {
            let g = post.opener_of[prev];
            let fh = if frame == NONE {
                Some(0)
            } else {
                post.height[frame]
            };
            post.parent[g] == frame
                && !post.reached[prev]
                && post.height[g].is_some()
                && post.height[g] == fh
        } else {
            false
        };
        if !ok {
            return Err(mismatch(format!(
                "post {} at {e} is never reached and does not follow a transfer",
                if e == n { "function end" } else { "end" }
            )));
        }
    }
    Ok(report)
}

/// An unconditional transfer: the stack is polymorphic after it.
fn is_transfer(op: u8) -> bool {
    matches!(op, 0x00 | 0x0c | 0x0e | 0x0f)
}

fn is_control(op: u8) -> bool {
    matches!(
        op,
        0x00 | 0x02 | 0x03 | 0x04 | 0x05 | 0x0b | 0x0c | 0x0d | 0x0e | 0x0f
    )
}

/// Continue a branch outcome to the side's next stop.
fn resume(side: &mut Side<'_>, walk: &mut Walk<'_>, s: Succ) -> Result<Point, TvFailure> {
    match s {
        (_, Some(ret), _) => Ok(Point::Return(ret)),
        (pc, None, stack) => advance(side, walk, pc, stack),
    }
}
