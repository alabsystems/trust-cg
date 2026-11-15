// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 24a: the exact merged-chain quotient (ruling OD-226 in
//! `docs/decision-record.md`).
//!
//! *The class.* `X86BlockMerge` joins a machine block `B` into its one
//! predecessor `A` when `A` ends in `jmp B`: it deletes the `jmp` and appends
//! `B`'s rows, their TV-1 stamps intact. The merged block then lowers rows of
//! several LIR blocks, and the one-to-one block correspondence of slice 6
//! ([`block_correspondence`]) does not hold.
//!
//! *Links, on the LIR alone* ([`link`]). An edge `x -> y` is a LINK exactly
//! when `x` ends in `Jump { dest: y }` (no argument or result), `y` is neither
//! `x` nor the entry block, and that `Jump` is the only edge into `y` from any
//! block of the source, reachable or not. Every run that executes `x`'s
//! `Jump` continues at `y`'s first instruction, every execution of `y`
//! follows that `Jump`, and a `Jump` with no argument transfers control and
//! does nothing else (the model `admit_blocks` applies to every `Jump`). So
//! CONTRACTING a link -- `x`'s instructions without its `Jump`, then `y`'s,
//! under `x`'s id -- is exact: the runs of the source and of the contraction
//! correspond one to one, with the same values, events and end. A `Brif`,
//! `Switch`, `Return` or `Trap` is never a link, even where a machine pass
//! folded it. Links form disjoint simple paths (each block has at most one
//! link in and one out), plus cycles in unreachable components.
//!
//! *Which chains: the stamps choose* ([`Quotient::of`]). The machine blocks
//! whose rows' stamps name two or more LIR blocks are visited first, then
//! those that name one, each phase in layout order. A visited block's chain
//! is the maximal path of links through the blocks it names and the
//! STAMP-SILENT blocks (no row of the machine names them); it is contracted
//! when it holds every block named, has two or more blocks, shares none with
//! an earlier chain, its absorbed members declare no parameter, its last
//! member does not branch to its head, the last member's copies into a loop
//! header's parameters do not run back into the previous member, and no row
//! is stamped with a removed `Jump` or past a member's end. Any other visited
//! block keeps today's refusal, which names why ([`Quotient::annotate`]). The
//! stamps are NOT trusted: they only choose which exact contractions are
//! stated; a choice the machine did not make breaks the correspondence on the
//! quotient (no claim) or is refuted.
//!
//! *The quotient pair.* `Q` is the source with each chain's instructions
//! concatenated under its head's id, without the `Jump`s between them; the
//! absorbed blocks leave `blocks`, `block_order` and `trust_ir_origins`;
//! nothing else changes. `X'` is the machine with every row's stamp `(member,
//! i)`, in every block, renumbered to `(head, first(member) + i)`; nothing
//! else changes. Stamps have no machine semantics, so `X'` is `X` as a
//! program. [`Quotient::check`] re-derives both from the original pair,
//! independently of the builder, in release builds, before any use.
//!
//! *The claim.* The theorem is built over `(Q, X')` by the unchanged slices
//! 1 to 23 and binds the ORIGINAL `(L, X)` ([`SourceBoundX86Body`]):
//! `X' ⊑ Q` (the theorem), `⟦Q⟧ = ⟦L⟧` (exact contraction) and `⟦X'⟧ = ⟦X⟧`
//! (only stamps differ) give `X ⊑ L`. Audit coordinates are mapped back
//! ([`Quotient::original`]).

use super::*;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
use trust_cg_lower::function::BasicBlock;
use trust_cg_lower::instructions::Instruction;
use trust_cg_lower::x86_64_isel::{X86ISelBlock, X86ISelConstPoolEntry, X86JumpTableData};

/// One block of a contracted chain: its first instruction's index in the
/// head's quotient block, how many of its instructions the quotient keeps
/// (all but its `Jump` for every member but the last, all for the last), and
/// its instruction count in the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Member {
    pub(super) block: Block,
    pub(super) first: usize,
    pub(super) kept: usize,
    pub(super) len: usize,
}

/// A source and machine with every chosen chain contracted (see the module
/// documentation), or the original pair borrowed when none is.
pub(super) struct Quotient<'a> {
    /// `Borrowed` exactly when no chain is contracted.
    source: Cow<'a, Function>,
    machine: Cow<'a, X86ISelFunction>,
    /// Each chain's head -> its members, head first.
    chains: BTreeMap<Block, Vec<Member>>,
    /// Each absorbed member (every member but a head) -> its head and the
    /// index of its first instruction there.
    absorbed: HashMap<Block, (Block, usize)>,
    /// Why the first several-block machine block in layout order that was
    /// not contracted was not ([`Self::annotate`]).
    first_note: Option<String>,
    /// Slice 24c (OD-228): the machine block [`Self::first_note`] describes
    /// ([`Self::first_note_at`]).
    first_note_at: Option<Block>,
    /// One above every block id of the original source and machine: a block
    /// a later rewrite adds (a slice-16 piece) never takes an absorbed
    /// member's id ([`split::rewrite_pieces`]).
    floor: u32,
}

/// One above the largest block id of `source` and `machine`: the first id
/// `split::rewrite_pieces` may give a new block of an uncontracted pair.
fn id_floor(source: &Function, machine: &X86ISelFunction) -> u32 {
    source
        .blocks
        .keys()
        .chain(machine.blocks.keys())
        .map(|block| block.0)
        .max()
        .unwrap_or(0)
        + 1
}

/// Every block of `source` that names each block as a successor,
/// deduplicated, reachable or not: its terminator's targets
/// ([`lir_successors`]) and both destinations of any `Invoke` it holds
/// (which admission refuses, counted so that no edge escapes the rule).
/// `dead` is the source's unreachable blocks, read only by a test mutant.
fn entering(source: &Function, dead: &BTreeSet<Block>) -> HashMap<Block, BTreeSet<Block>> {
    let mut entering: HashMap<Block, BTreeSet<Block>> = HashMap::new();
    for (block, body) in &source.blocks {
        if mutated("entering-live-only") && dead.contains(block) {
            continue;
        }
        let invokes = body
            .instructions
            .iter()
            .filter_map(|inst| match &inst.opcode {
                L::Invoke {
                    normal_dest,
                    unwind_dest,
                    ..
                } => Some([*normal_dest, *unwind_dest]),
                _ => None,
            })
            .flatten();
        for target in lir_successors(body).into_iter().chain(invokes) {
            entering.entry(target).or_default().insert(*block);
        }
    }
    entering
}

/// The block `x` links to ([`self`]'s rule (a)-(d)): `x` ends in `Jump {
/// dest: y }` with no argument or result, `y` has a body and is neither `x`
/// nor the entry block, and `x` is the only block of the source, reachable or
/// not, whose terminator targets `y`.
fn link(source: &Function, entering: &HashMap<Block, BTreeSet<Block>>, x: Block) -> Option<Block> {
    let last = source.blocks.get(&x)?.instructions.last()?;
    let L::Jump { dest } = last.opcode else {
        return None;
    };
    (last.args.is_empty()
        && last.results.is_empty()
        && dest != x
        && (dest != source.entry_block || mutated("allow-entry"))
        && source.blocks.contains_key(&dest)
        && entering
            .get(&dest)
            .is_some_and(|from| from.len() == 1 && from.contains(&x)))
    .then_some(dest)
}

/// Tests only (mutant `link-any-terminator`): a `Brif` or `Switch` into a
/// block no other edge enters is taken as a link to its smallest target.
fn any_terminator_link(
    source: &Function,
    entering: &HashMap<Block, BTreeSet<Block>>,
    x: Block,
) -> Option<Block> {
    let body = source.blocks.get(&x)?;
    lir_successors(body).into_iter().find(|y| {
        *y != x
            && *y != source.entry_block
            && source.blocks.contains_key(y)
            && entering
                .get(y)
                .is_some_and(|from| from.len() == 1 && from.contains(&x))
    })
}

/// The link of `x` under the active rule ([`link`]).
fn link_of(
    source: &Function,
    entering: &HashMap<Block, BTreeSet<Block>>,
    x: Block,
) -> Option<Block> {
    if mutated("link-any-terminator") {
        return any_terminator_link(source, entering, x);
    }
    link(source, entering, x)
}

/// The block that links to `y`, when one does.
fn linkpred(
    source: &Function,
    entering: &HashMap<Block, BTreeSet<Block>>,
    y: Block,
) -> Option<Block> {
    let from = entering.get(&y)?;
    let [x] = from.iter().copied().collect::<Vec<_>>()[..] else {
        return None;
    };
    (link_of(source, entering, x) == Some(y)).then_some(x)
}

/// The name of a LIR terminator, for a refusal.
fn terminator_name(body: &BasicBlock) -> &'static str {
    match body.instructions.last().map(|inst| &inst.opcode) {
        Some(L::Jump { .. }) => "Jump",
        Some(L::Brif { .. }) => "Brif",
        Some(L::Switch { .. }) => "Switch",
        Some(L::Return) => "Return",
        Some(L::Trap) => "Trap",
        _ => "non-terminator",
    }
}

/// LIR instruction equality for [`Quotient::check`]: `PartialEq`, but an
/// `Fconst` immediate compares by its bits, so the comparison is reflexive and
/// exact. `f64`'s `==` is not reflexive on a NaN (an unchanged `Fconst(NaN)`
/// would read as changed: the census refused `parse_inf_nan` so) and equates
/// `0.0` with `-0.0` (a builder that flipped a zero's sign would pass).
/// `Fconst` is the only LIR opcode with a float field; an instruction is
/// destructured exhaustively.
pub(crate) fn same_instruction(a: &Instruction, b: &Instruction) -> bool {
    let Instruction {
        opcode,
        args,
        results,
    } = a;
    let same_opcode = match (opcode, &b.opcode) {
        (
            L::Fconst { ty, imm },
            L::Fconst {
                ty: other,
                imm: bits,
            },
        ) if !mutated("check-float-eq") => ty == other && imm.to_bits() == bits.to_bits(),
        (opcode, other) => opcode == other,
    };
    same_opcode && *args == b.args && *results == b.results
}

/// [`same_instruction`] over two streams.
fn same_instructions(a: &[Instruction], b: &[Instruction]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_instruction(a, b))
}

/// The run of `Copy`s ending `body` that are the copies into `dest`'s
/// parameters ([`copy_run`]) of the tail of `chain`, measured over the
/// chain's concatenation and over the tail alone: when they differ, the
/// quotient's run would begin in an earlier member (refusal D10). Only a
/// loop header's edge copies are measured: they are the copies the
/// whole-body walk pairs (`CutEdge` and the loop pairing), which D10 keeps
/// the original's. On the parts route a planned or policy cut at a join
/// counts its edge copies over the quotient's block too; that run may be
/// longer than the original's, which is still exactly those instructions
/// (the quotient's pieces are admitted, design §2.7 and OD-226's claim).
fn copy_run_crosses(
    source: &Function,
    chain: &[Block],
    headers: &HashSet<Block>,
) -> Option<String> {
    let (&tail, earlier) = chain.split_last()?;
    let instructions = &source.blocks[&tail].instructions;
    let (last, body) = instructions.split_last()?;
    let L::Jump { dest } = last.opcode else {
        return None;
    };
    if !headers.contains(&dest) {
        return None;
    }
    let alone = copy_run(source, body, dest);
    let mut concatenation: Vec<Instruction> = Vec::new();
    for member in earlier {
        let instructions = &source.blocks[member].instructions;
        concatenation.extend_from_slice(&instructions[..instructions.len() - 1]);
    }
    concatenation.extend_from_slice(body);
    let previous = earlier.last().copied().unwrap_or(tail);
    (copy_run(source, &concatenation, dest) != alone).then(|| {
        format!(
            "the edge copies of LIR block {tail:?} into loop header {dest:?} would begin in LIR \
             block {previous:?}"
        )
    })
}

/// Refusals D5, D6, D10, D7 and D8 for a chain the stamps chose, the first
/// that fails.
fn chain_guards(
    source: &Function,
    machine: &X86ISelFunction,
    chain: &[Block],
    headers: &HashSet<Block>,
) -> Result<(), String> {
    let head = chain[0];
    if !mutated("allow-params") {
        for member in &chain[1..] {
            let count = source.blocks[member].params.len();
            if count > 0 {
                return Err(format!(
                    "LIR block {member:?}, which the chain from {head:?} would absorb, has \
                     {count} parameter(s)"
                ));
            }
        }
    }
    let tail = chain[chain.len() - 1];
    if !mutated("allow-self-loop") && lir_successors(&source.blocks[&tail]).contains(&head) {
        return Err(format!("the chain {chain:?} returns to its head {head:?}"));
    }
    if !mutated("copy-run-unchecked")
        && let Some(why) = copy_run_crosses(source, chain, headers)
    {
        return Err(why);
    }
    let mut blocks: Vec<&Block> = machine.blocks.keys().collect();
    blocks.sort_unstable();
    for block in blocks {
        for (row, inst) in machine.blocks[block].insts.iter().enumerate() {
            let Some(id) = inst.lowering_provenance.source_id() else {
                continue;
            };
            let Some(j) = chain.iter().position(|member| member.0 == id.block) else {
                continue;
            };
            let member = chain[j];
            let count = source.blocks[&member].instructions.len();
            let index = id.index as usize;
            if index >= count {
                return Err(format!(
                    "machine block {block:?} row {row} is stamped with instruction {index} of LIR \
                     block {member:?}, which has {count}"
                ));
            }
            if j + 1 < chain.len() && index + 1 == count && !mutated("allow-jump-stamp") {
                return Err(format!(
                    "machine block {block:?} row {row} is stamped with the Jump that ends LIR \
                     block {member:?}, which contracting the chain from {head:?} removes"
                ));
            }
        }
    }
    Ok(())
}

/// Why `missing`, a block machine block `machine_block` names, is not on the
/// chain `path` through `start` (refusals D1-D4).
#[allow(clippy::too_many_arguments)]
fn explain(
    source: &Function,
    entering: &HashMap<Block, BTreeSet<Block>>,
    dead: &BTreeSet<Block>,
    named: &BTreeSet<Block>,
    path: &[Block],
    missing: Block,
    claimed: &HashMap<Block, Block>,
    naming: &HashMap<Block, Vec<Block>>,
    machine_block: Block,
) -> String {
    let start = named.iter().next().copied().unwrap_or(missing);
    if missing == source.entry_block {
        return format!("LIR block {missing:?} is the entry block");
    }
    let from: Vec<Block> = entering
        .get(&missing)
        .map(|from| from.iter().copied().collect())
        .unwrap_or_default();
    match from.as_slice() {
        [] => format!(
            "LIR block {missing:?} is not on the chain of single-entry Jumps through {start:?} \
             (no block enters it)"
        ),
        [x] if link_of(source, entering, *x) != Some(missing) => {
            if *x == missing {
                format!("LIR blocks [{missing:?}] form a cycle of single-entry Jumps")
            } else {
                format!(
                    "the predecessor {x:?} of LIR block {missing:?} ends in a {}, not a Jump to it",
                    terminator_name(&source.blocks[x])
                )
            }
        }
        [x] => {
            let whose = if let Some(head) = claimed.get(x) {
                format!(" (its predecessor {x:?} is in the merged chain from {head:?})")
            } else if let Some(other) = naming
                .get(x)
                .and_then(|blocks| blocks.iter().find(|block| **block != machine_block))
            {
                format!(" (its predecessor {x:?} is lowered by machine block {other:?})")
            } else {
                String::new()
            };
            format!(
                "LIR block {missing:?} is not on the chain of single-entry Jumps through \
                 {start:?}{whose}"
            )
        }
        several => {
            let listed: Vec<String> = several
                .iter()
                .map(|block| {
                    if dead.contains(block) {
                        format!("{block:?} (unreachable)")
                    } else {
                        format!("{block:?}")
                    }
                })
                .collect();
            let on = several
                .iter()
                .find(|block| named.contains(block) || path.contains(block))
                .unwrap_or(&several[0]);
            format!(
                "LIR block {missing:?} is entered from [{}], not from {on:?} alone",
                listed.join(", ")
            )
        }
    }
}

impl<'a> Quotient<'a> {
    /// The original pair, contracted nowhere.
    pub(super) fn identity(source: &'a Function, machine: &'a X86ISelFunction) -> Self {
        Self {
            source: Cow::Borrowed(source),
            machine: Cow::Borrowed(machine),
            chains: BTreeMap::new(),
            absorbed: HashMap::new(),
            first_note: None,
            first_note_at: None,
            floor: id_floor(source, machine),
        }
    }

    /// Whether no chain is contracted (the pair is the original's).
    pub(super) fn is_identity(&self) -> bool {
        self.chains.is_empty()
    }

    /// The source the theorem states: `Q`, or the original.
    pub(super) fn source(&self) -> &Function {
        &self.source
    }

    /// The machine the theorem walks: `X'`, or the original.
    pub(super) fn machine(&self) -> &X86ISelFunction {
        &self.machine
    }

    /// One above every block id of the original pair.
    pub(super) fn floor(&self) -> u32 {
        self.floor
    }

    /// The chains contracted (their count, the blocks absorbed and their
    /// [`Self::describe`]), `None` for the identity.
    pub(super) fn merged(&self) -> Option<MergedChains> {
        (!self.is_identity()).then(|| MergedChains {
            chains: self.chains.len(),
            absorbed: self.absorbed.len(),
            described: self.describe(),
        })
    }

    /// Slice 24c (OD-228): the machine block whose decline
    /// [`Self::annotate`] appends, when there is one: a refusal that names
    /// another block over segments carries no such note
    /// ([`super::segment::correspondence`]).
    pub(super) fn first_note_at(&self) -> Option<Block> {
        self.first_note_at
    }

    /// `reason` (a correspondence refusal), with why the first several-block
    /// machine block was not contracted, when it was considered.
    pub(super) fn annotate(&self, reason: String) -> String {
        match &self.first_note {
            Some(note) => format!("{reason}; not contracted: {note}"),
            None => reason,
        }
    }

    /// The contracted chains, in the ORIGINAL ids: `Block(h)=[Block(h),
    /// Block(c1), ...]; ...`.
    pub(super) fn describe(&self) -> String {
        self.chains
            .iter()
            .map(|(head, members)| {
                let blocks: Vec<String> = members
                    .iter()
                    .map(|member| format!("{:?}", member.block))
                    .collect();
                format!("{head:?}=[{}]", blocks.join(", "))
            })
            .collect::<Vec<_>>()
            .join("; ")
    }

    /// A refusal of the route over a non-identity quotient, as the owner
    /// reports it: every `Unsupported` but the empty observable (OD-115)
    /// names the chains ([`X86BodyUnsupported::OverQuotient`]); a mismatch
    /// names machine rows, blocks and counts, which `X'` shares with `X`, and
    /// is returned as it is.
    pub(super) fn over(&self, refusal: X86BodyRefusal) -> X86BodyRefusal {
        if self.is_identity() {
            return refusal;
        }
        over_chains(&self.describe(), refusal)
    }

    /// A LIR location of the quotient as the original's. A join's location
    /// (`JOIN_ROW`) keeps its block: a join is only ever a head, since an
    /// absorbed member has one entering edge. A location of a head's block is
    /// the one member whose kept range holds it (a member that keeps nothing
    /// holds none), every other location its own.
    pub(super) fn original(&self, block: Block, index: usize) -> (Block, usize) {
        if index == JOIN_ROW {
            return (block, index);
        }
        let Some(members) = self.chains.get(&block) else {
            return (block, index);
        };
        if mutated("original-first-match") {
            // The first member whose whole block, its removed `Jump`
            // included, would cover the location.
            let member = members
                .iter()
                .find(|member| member.first <= index && index < member.first + member.len)
                .unwrap_or_else(|| members.last().expect("a chain has members"));
            return (member.block, index - member.first);
        }
        let tail = members.last().expect("a chain has members");
        let member = members
            .iter()
            .find(|member| member.first <= index && index < member.first + member.kept)
            .unwrap_or(tail);
        (member.block, index - member.first)
    }

    /// An original LIR location in the quotient's coordinates, `None` exactly
    /// at a `Jump` the quotient removes. An index past a member's end maps
    /// past its head block's end (so no rewrite takes it for an instruction
    /// of the quotient). Never used to rewrite a stamp (refusals D7 and D8
    /// exclude those first).
    pub(super) fn to_quotient(&self, block: Block, index: usize) -> Option<(Block, usize)> {
        let Some(&(head, _)) = self.absorbed.get(&block) else {
            if self.chains.contains_key(&block) {
                return self.within(block, block, index);
            }
            return Some((block, index));
        };
        self.within(head, block, index)
    }

    fn within(&self, head: Block, block: Block, index: usize) -> Option<(Block, usize)> {
        let members = &self.chains[&head];
        let member = members
            .iter()
            .find(|member| member.block == block)
            .expect("a member of its chain");
        let total: usize = members.iter().map(|member| member.kept).sum();
        if index < member.kept {
            Some((head, member.first + index))
        } else if index < member.len {
            None
        } else {
            Some((head, total + (index - member.len)))
        }
    }

    /// The quotient of `source` and `machine` the stamps choose (see the
    /// module documentation), checked ([`Self::check`]): the identity when
    /// no chain qualifies. `cfg` is the source's own control flow (its loop
    /// headers and dead blocks). A failed check is
    /// [`X86BodyUnsupported::Construction`], never credit.
    pub(super) fn of(
        source: &'a Function,
        machine: &'a X86ISelFunction,
        cfg: &SourceCfg,
    ) -> Result<Self, X86BodyRefusal> {
        let entering = entering(source, &cfg.dead);
        let headers: HashSet<Block> = cfg.loops.iter().map(|lp| lp.header).collect();
        let tables = dispatch_blocks(machine);
        let named_by = |block: &Block| -> BTreeSet<Block> {
            machine
                .blocks
                .get(block)
                .map(|body| {
                    body.insts
                        .iter()
                        .filter_map(|inst| inst.lowering_provenance.source_id())
                        .map(|id| Block(id.block))
                        .collect()
                })
                .unwrap_or_default()
        };
        let anywhere: HashSet<Block> = machine
            .blocks
            .values()
            .flat_map(|body| &body.insts)
            .filter_map(|inst| inst.lowering_provenance.source_id())
            .map(|id| Block(id.block))
            .collect();
        let silent =
            |block: Block| source.blocks.contains_key(&block) && !anywhere.contains(&block);
        // Each LIR block -> the laid-out machine blocks whose rows name it.
        let mut naming: HashMap<Block, Vec<Block>> = HashMap::new();
        for block in &machine.block_order {
            for lir in named_by(block) {
                naming.entry(lir).or_default().push(*block);
            }
        }
        let mut claimed: HashMap<Block, Block> = HashMap::new();
        let mut paths: BTreeMap<Block, Vec<Block>> = BTreeMap::new();
        let mut chosen: HashSet<Block> = HashSet::new();
        let mut declined: HashMap<Block, String> = HashMap::new();
        let phases = if mutated("single-first") {
            [false, true]
        } else {
            [true, false]
        };
        for several in phases {
            for block in &machine.block_order {
                if tables.contains_key(block) {
                    continue;
                }
                let named = named_by(block);
                if named.is_empty() || (named.len() >= 2) != several {
                    continue;
                }
                if named.iter().any(|lir| !source.blocks.contains_key(lir)) {
                    continue;
                }
                if let Some((member, head)) = named
                    .iter()
                    .find_map(|lir| claimed.get(lir).map(|head| (*lir, *head)))
                {
                    if several {
                        declined.insert(
                            *block,
                            format!("LIR block {member:?} is in the merged chain from {head:?}"),
                        );
                    }
                    continue;
                }
                let every = mutated("contract-all-rule-chains");
                let in_set = |lir: Block, fill: bool| {
                    (named.contains(&lir) || (fill && silent(lir)) || every)
                        && !claimed.contains_key(&lir)
                };
                // Back from the smallest named block through silent heads,
                // then forward through silent tails.
                let smallest = *named.iter().next().expect("a named block");
                let mut start = smallest;
                let mut walked = vec![smallest];
                let mut cycle = false;
                while let Some(x) = linkpred(source, &entering, start) {
                    if !in_set(x, !mutated("no-backward-fill")) {
                        break;
                    }
                    if walked.contains(&x) {
                        cycle = true;
                        break;
                    }
                    walked.push(x);
                    start = x;
                }
                if cycle {
                    walked.sort_unstable();
                    declined.insert(
                        *block,
                        format!("LIR blocks {walked:?} form a cycle of single-entry Jumps"),
                    );
                    continue;
                }
                let mut path = vec![start];
                while let Some(y) = link_of(source, &entering, *path.last().expect("a start")) {
                    if !in_set(y, !mutated("no-forward-fill")) || path.contains(&y) {
                        break;
                    }
                    path.push(y);
                }
                if let Some(missing) = named.iter().find(|lir| !path.contains(lir)) {
                    if several {
                        declined.insert(
                            *block,
                            explain(
                                source, &entering, &cfg.dead, &named, &path, *missing, &claimed,
                                &naming, *block,
                            ),
                        );
                    }
                    continue;
                }
                if path.len() == 1 {
                    continue;
                }
                if let Err(why) = chain_guards(source, machine, &path, &headers) {
                    declined.insert(*block, why);
                    continue;
                }
                for member in &path {
                    claimed.insert(*member, path[0]);
                }
                chosen.insert(*block);
                paths.insert(path[0], path);
            }
        }
        // The first several-block machine block not contracted: the one the
        // correspondence over the result reports.
        let first_several = machine
            .block_order
            .iter()
            .filter(|block| !tables.contains_key(*block) && !chosen.contains(*block))
            .find(|block| named_by(block).len() >= 2)
            .copied();
        let first_note = first_several.and_then(|block| declined.get(&block).cloned());
        let first_note_at = first_several.filter(|_| first_note.is_some());
        if paths.is_empty() {
            let mut identity = Self::identity(source, machine);
            identity.first_note = first_note;
            identity.first_note_at = first_note_at;
            return Ok(identity);
        }
        let mut quotient = build(source, machine, &paths, &chosen, first_note);
        quotient.first_note_at = first_note_at;
        if !mutated("check-off")
            && let Err(detail) = quotient.check(source, machine, &headers)
        {
            return Err(
                quotient.over(unsupported(X86BodyUnsupported::Construction(format!(
                    "the merged-chain quotient is not the exact contraction of its source and \
                 machine: {detail}"
                )))),
            );
        }
        Ok(quotient)
    }

    /// THE check of a quotient (slice 24a's trusted code): it re-derives the
    /// quotient pair from the original `source` and `machine` independently
    /// of the builder, with its own entering edges and links, and holds
    /// exactly when
    ///
    /// - (i) every chain is a path of links on `source` from its head (each
    ///   member's offsets as the module documentation states; its absorbed
    ///   members disjoint from every other chain's, declaring no parameter
    ///   and absent from the quotient), each head is the concatenation of its
    ///   chain with the head's parameters, its terminator does not branch to
    ///   the head, and the last member's loop-edge copies stay inside it;
    /// - (ii) every other block, its locations and origins, the block order
    ///   (minus the absorbed blocks) and every other field of the source are
    ///   unchanged, field by field (an exhaustive destructuring: a new
    ///   `Function` field breaks this build);
    /// - (iii) the machine is unchanged but for each row's stamp, whose new
    ///   coordinates are the forward map of its old ones and name an equal
    ///   instruction (exhaustive over `X86ISelBlock` and `X86ISelInst`;
    ///   `X86ISelFunction`'s public fields by name, and every field, the
    ///   crate-private ones no pattern outside `trust-cg-lower` may name
    ///   included, through its canonical verifier identity with the original
    ///   stamps restored: that writer destructures the struct exhaustively,
    ///   so a new field breaks its build until the identity renders it).
    ///
    /// It runs in every build, before the quotient is used.
    fn check(
        &self,
        source: &Function,
        machine: &X86ISelFunction,
        headers: &HashSet<Block>,
    ) -> Result<(), String> {
        let q: &Function = &self.source;
        let x: &X86ISelFunction = &self.machine;
        if self.floor != id_floor(source, machine) {
            return Err("the id floor is not one above the original pair's block ids".into());
        }
        // Its own entering edges: every block an instruction of any block,
        // reachable or not, names. The opcodes that name a block are exactly
        // `Jump`, `Brif`, `Switch` and `Invoke` (every `Block` field of the
        // LIR `Opcode`), each counted wherever it stands.
        let targets = |inst: &Instruction| -> Vec<Block> {
            match &inst.opcode {
                L::Jump { dest } => vec![*dest],
                L::Brif {
                    then_dest,
                    else_dest,
                    ..
                } => vec![*then_dest, *else_dest],
                L::Switch { cases, default } => cases
                    .iter()
                    .map(|(_, target)| *target)
                    .chain(std::iter::once(*default))
                    .collect(),
                L::Invoke {
                    normal_dest,
                    unwind_dest,
                    ..
                } => vec![*normal_dest, *unwind_dest],
                _ => Vec::new(),
            }
        };
        let mut into: HashMap<Block, BTreeSet<Block>> = HashMap::new();
        for (block, body) in &source.blocks {
            for inst in &body.instructions {
                for target in targets(inst) {
                    into.entry(target).or_default().insert(*block);
                }
            }
        }
        let links = |x: Block, y: Block| -> bool {
            let jump = source
                .blocks
                .get(&x)
                .and_then(|body| body.instructions.last())
                .is_some_and(|last| {
                    matches!(last.opcode, L::Jump { dest } if dest == y)
                        && last.args.is_empty()
                        && last.results.is_empty()
                });
            (jump || mutated("check-any-terminator-link"))
                && x != y
                && (y != source.entry_block || mutated("check-entry-link"))
                && source.blocks.contains_key(&y)
                && into
                    .get(&y)
                    .is_some_and(|from| from.len() == 1 && from.contains(&x))
        };
        // (i) The chains.
        let mut members_seen: HashSet<Block> = HashSet::new();
        let mut forward: HashMap<u32, (Block, usize, usize)> = HashMap::new();
        let mut absorbed_seen = 0usize;
        for (head, members) in &self.chains {
            let Some(first_member) = members.first() else {
                return Err(format!("the chain from {head:?} has no member"));
            };
            if first_member.block != *head || first_member.first != 0 || members.len() < 2 {
                return Err(format!(
                    "the chain from {head:?} does not start at its head"
                ));
            }
            let mut first = 0usize;
            let mut concatenation: Vec<Instruction> = Vec::new();
            let mut locs: Vec<Option<trust_cg_ir::SourceLoc>> = Vec::new();
            let mut origins: Vec<Option<trust_cg_ir::TrustIrInstId>> = Vec::new();
            let mut any_locs = false;
            let mut any_origins = false;
            for (j, member) in members.iter().enumerate() {
                let Some(body) = source.blocks.get(&member.block) else {
                    return Err(format!("member {:?} has no source block", member.block));
                };
                let len = body.instructions.len();
                let last = j + 1 == members.len();
                if len == 0 {
                    return Err(format!("member {:?} is empty", member.block));
                }
                let kept = if last { len } else { len - 1 };
                if member.len != len || member.kept != kept || member.first != first {
                    return Err(format!(
                        "member {:?} of the chain from {head:?} has the wrong offsets",
                        member.block
                    ));
                }
                if !members_seen.insert(member.block) {
                    return Err(format!("{:?} is a member of two chains", member.block));
                }
                if j > 0 {
                    let previous = members[j - 1].block;
                    if !links(previous, member.block) {
                        return Err(format!(
                            "{previous:?} -> {:?} is not a link of the source",
                            member.block
                        ));
                    }
                    if !body.params.is_empty() {
                        return Err(format!("absorbed {:?} declares parameters", member.block));
                    }
                    if q.blocks.contains_key(&member.block)
                        || q.trust_ir_origins.contains_key(&member.block)
                    {
                        return Err(format!("absorbed {:?} is still a block", member.block));
                    }
                    if self.absorbed.get(&member.block) != Some(&(*head, first)) {
                        return Err(format!("absorbed {:?} is mapped wrongly", member.block));
                    }
                    absorbed_seen += 1;
                }
                concatenation.extend_from_slice(&body.instructions[..kept]);
                any_locs |= !body.source_locs.is_empty();
                locs.extend((0..kept).map(|i| body.source_locs.get(i).copied().flatten()));
                let member_origins = source.trust_ir_origins.get(&member.block);
                any_origins |= member_origins.is_some();
                origins.extend(
                    (0..kept).map(|i| member_origins.and_then(|o| o.get(i).copied().flatten())),
                );
                forward.insert(member.block.0, (*head, first, kept));
                first += kept;
            }
            let (Some(original), Some(contracted)) = (source.blocks.get(head), q.blocks.get(head))
            else {
                return Err(format!("the head {head:?} is not a block of both sources"));
            };
            let BasicBlock {
                params,
                instructions,
                source_locs,
            } = contracted;
            if *params != original.params {
                return Err(format!("the head {head:?} changed its parameters"));
            }
            if !same_instructions(instructions, &concatenation) {
                return Err(format!(
                    "the head {head:?} is not the concatenation of its chain"
                ));
            }
            if *source_locs != if any_locs { locs } else { Vec::new() } {
                return Err(format!(
                    "the head {head:?}'s source locations are not its chain's"
                ));
            }
            if q.trust_ir_origins.get(head) != any_origins.then_some(&origins) {
                return Err(format!(
                    "the head {head:?}'s trust-ir origins are not its chain's"
                ));
            }
            if instructions
                .last()
                .is_some_and(|last| targets(last).contains(head))
            {
                return Err(format!("the chain from {head:?} returns to its head"));
            }
            if let Some(why) = copy_run_crosses(
                source,
                &members
                    .iter()
                    .map(|member| member.block)
                    .collect::<Vec<_>>(),
                headers,
            ) {
                return Err(why);
            }
        }
        if absorbed_seen != self.absorbed.len() {
            return Err("the absorbed map names a block no chain absorbs".into());
        }
        // (ii) The rest of the source.
        for (block, original) in &source.blocks {
            if self.chains.contains_key(block) || self.absorbed.contains_key(block) {
                continue;
            }
            let Some(BasicBlock {
                params,
                instructions,
                source_locs,
            }) = q.blocks.get(block)
            else {
                return Err(format!("{block:?} is missing from the quotient"));
            };
            if *params != original.params
                || !same_instructions(instructions, &original.instructions)
                || *source_locs != original.source_locs
            {
                return Err(format!("{block:?} changed"));
            }
        }
        if q.blocks.len() + self.absorbed.len() != source.blocks.len() {
            return Err("the quotient has blocks the source does not".into());
        }
        let order: Vec<Block> = source
            .block_order
            .iter()
            .filter(|block| !self.absorbed.contains_key(*block))
            .copied()
            .collect();
        let Function {
            name,
            signature,
            blocks: _,
            block_order,
            trust_ir_origins,
            entry_block,
            stack_slots,
            value_types,
            pure_callees,
            libm_pure_callees,
            debug_meta,
            debug_value_bindings,
            stack_protector,
            stack_limit,
            param_pointee_types,
            abi_sret_param,
            sret_arg_callees,
            sret_arg_indirect_callees,
            eh_info,
            eh_type_table,
            target_features,
        } = q;
        if *block_order != order {
            return Err("the block order is not the source's without the absorbed blocks".into());
        }
        for (block, origins) in trust_ir_origins {
            if !self.chains.contains_key(block)
                && source.trust_ir_origins.get(block) != Some(origins)
            {
                return Err(format!("{block:?}'s trust-ir origins changed"));
            }
        }
        for (block, origins) in &source.trust_ir_origins {
            if !self.chains.contains_key(block)
                && !self.absorbed.contains_key(block)
                && trust_ir_origins.get(block) != Some(origins)
            {
                return Err(format!("{block:?}'s trust-ir origins changed"));
            }
        }
        let trust_cg_lower::function::Signature { params, returns } = signature;
        // `FunctionDebugMeta` is not `PartialEq`: compared as its serde value.
        fn debug<T: serde::Serialize>(meta: &T) -> Result<serde_json::Value, String> {
            serde_json::to_value(meta).map_err(|error| error.to_string())
        }
        let unchanged = *name == source.name
            && *params == source.signature.params
            && *returns == source.signature.returns
            && *entry_block == source.entry_block
            && *stack_slots == source.stack_slots
            && *value_types == source.value_types
            && *pure_callees == source.pure_callees
            && *libm_pure_callees == source.libm_pure_callees
            && debug(debug_meta)? == debug(&source.debug_meta)?
            && *debug_value_bindings == source.debug_value_bindings
            && *stack_protector == source.stack_protector
            && *stack_limit == source.stack_limit
            && *param_pointee_types == source.param_pointee_types
            && *abi_sret_param == source.abi_sret_param
            && *sret_arg_callees == source.sret_arg_callees
            && *sret_arg_indirect_callees == source.sret_arg_indirect_callees
            && *eh_info == source.eh_info
            && *eh_type_table == source.eh_type_table
            && *target_features == source.target_features;
        if !unchanged {
            return Err("a field of the source other than its blocks changed".into());
        }
        // (iii) The machine, up to its stamps.
        let forward_id = |id: SourceInstId| -> Result<SourceInstId, String> {
            match forward.get(&id.block) {
                None => Ok(id),
                Some(&(head, first, kept)) if (id.index as usize) < kept => Ok(SourceInstId {
                    block: head.0,
                    index: (first + id.index as usize) as u32,
                }),
                Some(_) => Err(format!(
                    "a row is stamped with instruction {} of member {:?}, which the quotient \
                     does not keep",
                    id.index, id.block
                )),
            }
        };
        fn instruction(function: &Function, id: SourceInstId) -> Option<&Instruction> {
            function
                .blocks
                .get(&Block(id.block))
                .and_then(|body| body.instructions.get(id.index as usize))
        }
        let X86ISelFunction {
            name,
            sig,
            blocks,
            block_order,
            next_vreg,
            stack_slots,
            const_pool_entries,
            jump_tables,
            max_outgoing_call_bytes,
            vreg_nominal_widths,
            guard_obligations,
            eh_info,
            current_lowering_provenance,
            source_mir_inst_count,
            // Crate-private to `trust-cg-lower` (no pattern here may name
            // them): compared through the canonical identity below, whose
            // writer destructures every field of `X86ISelFunction` by name
            // with no `..` (a new field, public or not, breaks that build
            // until the identity renders it).
            ..
        } = x;
        let pool_equal = const_pool_entries.len() == machine.const_pool_entries.len()
            && const_pool_entries
                .iter()
                .zip(&machine.const_pool_entries)
                .all(|(new, old)| {
                    let X86ISelConstPoolEntry { data, align } = new;
                    *data == old.data && *align == old.align
                });
        let tables_equal = jump_tables.len() == machine.jump_tables.len()
            && jump_tables
                .iter()
                .zip(&machine.jump_tables)
                .all(|(new, old)| {
                    let X86JumpTableData { min_val, targets } = new;
                    *min_val == old.min_val && *targets == old.targets
                });
        let unchanged = *name == machine.name
            && sig.params == machine.sig.params
            && sig.returns == machine.sig.returns
            && *block_order == machine.block_order
            && *next_vreg == machine.next_vreg
            && *stack_slots == machine.stack_slots
            && pool_equal
            && tables_equal
            && *max_outgoing_call_bytes == machine.max_outgoing_call_bytes
            && *vreg_nominal_widths == machine.vreg_nominal_widths
            && *guard_obligations == machine.guard_obligations
            && *eh_info == machine.eh_info
            && *current_lowering_provenance == machine.current_lowering_provenance
            && *source_mir_inst_count == machine.source_mir_inst_count
            && blocks.len() == machine.blocks.len();
        if !unchanged {
            return Err("a field of the machine other than its rows' stamps changed".into());
        }
        let mut restored = x.clone();
        for (block, old) in &machine.blocks {
            let Some(X86ISelBlock { insts, successors }) = blocks.get(block) else {
                return Err(format!("machine block {block:?} is missing"));
            };
            if *successors != old.successors || insts.len() != old.insts.len() {
                return Err(format!("machine block {block:?} changed"));
            }
            for (row, (new, before)) in insts.iter().zip(&old.insts).enumerate() {
                let X86ISelInst {
                    opcode,
                    operands: _,
                    flags,
                    proof_origin,
                    call_arg_regs,
                    call_result_regs,
                    internal_return_regs,
                    lowering_provenance,
                } = new;
                if *opcode != before.opcode
                    || *flags != before.flags
                    || *proof_origin != before.proof_origin
                    || *call_arg_regs != before.call_arg_regs
                    || *call_result_regs != before.call_result_regs
                    || *internal_return_regs != before.internal_return_regs
                {
                    return Err(format!("machine block {block:?} row {row} changed"));
                }
                match (before.lowering_provenance, *lowering_provenance) {
                    (
                        LoweringProvenance::SourceInst {
                            id: old_id,
                            digest: old_digest,
                            trust_ir_inst: old_inst,
                        },
                        LoweringProvenance::SourceInst {
                            id,
                            digest,
                            trust_ir_inst,
                        },
                    ) => {
                        if digest != old_digest
                            || trust_ir_inst != old_inst
                            || id != forward_id(old_id)?
                            || !match (instruction(q, id), instruction(source, old_id)) {
                                (Some(stated), Some(original)) => {
                                    same_instruction(stated, original)
                                }
                                (stated, original) => stated.is_none() && original.is_none(),
                            }
                        {
                            return Err(format!(
                                "machine block {block:?} row {row}'s stamp is not the forward \
                                 map of its original"
                            ));
                        }
                    }
                    (
                        LoweringProvenance::Synthetic { reason: old },
                        LoweringProvenance::Synthetic { reason },
                    ) if reason == old => {}
                    _ => {
                        return Err(format!(
                            "machine block {block:?} row {row} changed its provenance kind"
                        ));
                    }
                }
                restored
                    .blocks
                    .get_mut(block)
                    .expect("a machine block")
                    .insts[row]
                    .lowering_provenance = before.lowering_provenance;
            }
        }
        // Every field, the operands' float payloads and the crate-private
        // tables included, once the original stamps are restored.
        let identity = |function: &X86ISelFunction| {
            function
                .canonical_verifier_identity_bytes()
                .map_err(|error| error.to_string())
        };
        if identity(&restored)? != identity(machine)? {
            return Err("the machine differs from the original by more than its stamps".into());
        }
        Ok(())
    }
}

/// The quotient pair for the chosen `paths` (head -> members), as the
/// module documentation states it; [`Quotient::check`] re-derives it.
fn build<'a>(
    source: &Function,
    machine: &X86ISelFunction,
    paths: &BTreeMap<Block, Vec<Block>>,
    chosen: &HashSet<Block>,
    first_note: Option<String>,
) -> Quotient<'a> {
    let mut chains: BTreeMap<Block, Vec<Member>> = BTreeMap::new();
    let mut absorbed: HashMap<Block, (Block, usize)> = HashMap::new();
    for (head, path) in paths {
        let mut first = 0usize;
        let mut members = Vec::with_capacity(path.len());
        for (j, block) in path.iter().enumerate() {
            let len = source.blocks[block].instructions.len();
            let kept = if j + 1 < path.len() { len - 1 } else { len };
            members.push(Member {
                block: *block,
                first,
                kept,
                len,
            });
            if j > 0 {
                absorbed.insert(*block, (*head, first));
            }
            first += kept;
        }
        chains.insert(*head, members);
    }
    let mut q = source.clone();
    for (head, members) in &chains {
        let mut instructions: Vec<Instruction> = Vec::new();
        let mut locs = Vec::new();
        let mut origins = Vec::new();
        let any_locs = members
            .iter()
            .any(|member| !source.blocks[&member.block].source_locs.is_empty());
        let any_origins = members
            .iter()
            .any(|member| source.trust_ir_origins.contains_key(&member.block));
        for (j, member) in members.iter().enumerate() {
            let body = &source.blocks[&member.block];
            let kept = &body.instructions[..member.kept];
            if mutated("builder-drop-member-instructions") && j > 0 {
                instructions.extend_from_slice(&kept[kept.len().min(1)..]);
            } else {
                instructions.extend_from_slice(kept);
            }
            locs.extend((0..member.kept).map(|i| body.source_locs.get(i).copied().flatten()));
            let member_origins = source.trust_ir_origins.get(&member.block);
            origins.extend(
                (0..member.kept).map(|i| member_origins.and_then(|o| o.get(i).copied().flatten())),
            );
        }
        let block = q.blocks.get_mut(head).expect("a head is a block");
        block.instructions = instructions;
        block.source_locs = if any_locs { locs } else { Vec::new() };
        if any_origins {
            q.trust_ir_origins.insert(*head, origins);
        } else {
            q.trust_ir_origins.remove(head);
        }
    }
    if mutated("builder-flip-zero") {
        for (block, body) in q.blocks.iter_mut() {
            if chains.contains_key(block) {
                continue;
            }
            for inst in &mut body.instructions {
                if let L::Fconst { imm, .. } = &mut inst.opcode
                    && imm.to_bits() == (-0.0f64).to_bits()
                {
                    *imm = 0.0;
                }
            }
        }
    }
    for member in absorbed.keys() {
        q.blocks.remove(member);
        q.trust_ir_origins.remove(member);
    }
    q.block_order.retain(|block| !absorbed.contains_key(block));
    if mutated("builder-drop-value-types") {
        q.value_types.clear();
    }
    // Every row's stamp, in every block (laid out, dispatch, search or dead).
    let mut forward: HashMap<u32, (Block, usize)> = HashMap::new();
    for (head, members) in &chains {
        for member in members {
            let first = if mutated("builder-wrong-offset") && member.block != *head {
                member.first + 1
            } else {
                member.first
            };
            forward.insert(member.block.0, (*head, first));
        }
    }
    let mut x = machine.clone();
    for (block, body) in x.blocks.iter_mut() {
        if mutated("rewrite-merged-block-only") && !chosen.contains(block) {
            continue;
        }
        for inst in &mut body.insts {
            if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance
                && let Some((head, first)) = forward.get(&id.block)
            {
                id.block = head.0;
                id.index = (first + id.index as usize) as u32;
            }
        }
    }
    if mutated("builder-const-pool")
        && let Some(entry) = x.const_pool_entries.first_mut()
        && let Some(byte) = entry.data.last_mut()
    {
        *byte ^= 0x40;
    }
    Quotient {
        source: Cow::Owned(q),
        machine: Cow::Owned(x),
        chains,
        absorbed,
        first_note,
        first_note_at: None,
        floor: id_floor(source, machine),
    }
}

/// Whether mutant `name` is active (tests only; always `false` otherwise).
#[cfg(test)]
pub(super) fn mutated(name: &str) -> bool {
    mutant::is(name)
}

/// Whether mutant `name` is active (tests only; always `false` otherwise).
#[cfg(not(test))]
#[inline(always)]
pub(super) const fn mutated(_name: &str) -> bool {
    false
}

/// Tests only: the mutants of slice 24a's non-vacuity controls (design
/// §5.5), named `s25-*`, of slice 25's scaled-index and read-modify-write
/// rules (OD-227), named `s24c-*`, of slice 24c's segment rules (OD-228,
/// [`super::segment`]) and, named `od233-*`, of OD-233's defined cut inputs
/// (`split::cut_definitions`, `build_theorem`). While a guard lives, this
/// thread's quotient, its wiring, the body walk and the statement in parts
/// run with each rule it names broken; each must make a control fail
/// (`x86_source_bound_body::tests::slice24`, `::slice25`, `::slice24c` and
/// `::od233`). Only a guard activates one: no
/// environment variable does, so no inherited setting can reach a
/// qualification or credit lane, and a thread with no guard runs the real
/// rules.
#[cfg(test)]
pub(crate) mod mutant {
    use std::cell::RefCell;

    thread_local! {
        static ACTIVE: RefCell<Option<String>> = const { RefCell::new(None) };
    }

    /// Whether mutant `name` is active on this thread.
    pub(crate) fn is(name: &str) -> bool {
        ACTIVE.with(|active| {
            active
                .borrow()
                .as_deref()
                .is_some_and(|list| list.split(',').any(|item| item.trim() == name))
        })
    }

    /// The mutants active on this thread, comma-separated (`""`: none).
    pub(crate) fn active() -> String {
        ACTIVE.with(|active| active.borrow().clone().unwrap_or_default())
    }

    /// Activate `names` (comma-separated) on this thread until the guard
    /// drops (`""`: none).
    pub(crate) fn set(names: &str) -> Guard {
        let before = ACTIVE.with(|active| active.replace(Some(names.to_owned())));
        Guard(before)
    }

    pub(crate) struct Guard(Option<String>);

    impl Drop for Guard {
        fn drop(&mut self) {
            let before = self.0.take();
            ACTIVE.with(|active| *active.borrow_mut() = before);
        }
    }
}
