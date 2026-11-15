// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 24c: segments, the if-converted regions (ruling OD-228 in
//! `docs/decision-record.md`).
//!
//! *The class.* `X86IfConvert` keeps a diamond's header rows before its
//! branch, replaces the `jcc; jmp` by the arms' flag-free computes (stamped
//! clones), an unattributed `mov` and `cmov` and a `jmp` to the join, and
//! deletes both arms; an arm that only copied a value leaves no row at all
//! (it is STAMP-SILENT). The one machine block then lowers rows of several
//! LIR blocks, or names one LIR block whose arms have no machine block, and
//! the one-to-one block correspondence of slice 6 does not hold.
//!
//! *The rule, on the stated LIR* (the source, or slice 24a's merged-chain
//! quotient: [`check`]). A SEGMENT is a head `h`, members `S` (`h` first,
//! then the source's topological order) and one laid-out machine block `m`
//! that lowers them all:
//!
//! - (C1) `h` has a body and is live; `m` is laid out and is neither a
//!   jump-table dispatch nor a binary-search block;
//! - (C2) every member but `h` is live, is not the entry, has every live
//!   predecessor in `S` and is reached from `h` along edges inside `S`;
//! - (C3) every edge between members runs forward in the topological order
//!   and no member branches to `h` (so `S` is acyclic, and no member but `h`
//!   is a loop header: C4);
//! - (C5) every member, `h` included, ends in `Jump`, `Brif` or `Switch`;
//! - (C6) no EXIT (an edge `(s, z)`, `s` in `S`, `z` not) enters a loop
//!   header;
//! - (C7) no successor of `m` is a dispatch or search block, and no row of
//!   `m` names a jump-table index;
//! - (C0) `h` is among the LIR blocks `m`'s rows name, which are all members
//!   with bodies; segments are disjoint, their machine blocks distinct; every
//!   live predecessor of `h` lies outside `S`.
//!
//! Dead entering edges are not counted: nothing is rewritten, and a dead
//! block's machine block is off the chain by the dead-block induction
//! ([`block_correspondence`]).
//!
//! *The stamps choose* ([`choose`]): `S` is the blocks `m`'s stamps name and
//! the stamp-silent blocks the rule admits. They are NOT trusted: [`check`]
//! re-derives every condition from the LIR and the machine's stamps with its
//! own live-predecessor map, in every build, before any use, and a chosen set
//! it refuses is [`X86BodyUnsupported::Construction`], never credit.
//!
//! *The statement.* `lowering` stays one-to-one (`h -> m`); `m`'s successors
//! must be exactly the exit targets ([`block_correspondence_over`]). `m` is
//! walked whole, once per exit target, from `h`'s entry state, against the
//! program of the EFFECT MEMBER `E` ([`effect_member`]): every call, incoming
//! access, rounding operation, stop and indexed access of `S` lies in `E`,
//! which every run through `S` passes (C9; C10: no internal join of `S` has
//! a private byte OD-192 leaves dead). Each exit `(s, z)` claims `(or (not
//! G_{s,z}) M_{m->z})` under `running`; internal edges claim nothing; the
//! other members walk no rows and state no items, which [`guard_members`]
//! re-checks where the theorem consumes the walks, re-deriving `E` (C11). Per path,
//! consecutive members take no machine step. The solver judges the `cmov`
//! against the diamond's values at the join: nothing of `X86IfConvert`'s
//! admission or speculation rules is assumed.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

/// What a segment's internal edges are, for the trace line
/// ([`Segments::stated`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum SegmentKind {
    /// Some internal edge leaves a `Brif` or `Switch`, and the machine
    /// block's rows name two or more members (an if-converted diamond, a
    /// `Switch` of two cases, a triangle).
    Diamond,
    /// As [`Self::Diamond`], but the rows name the head alone: every other
    /// member is stamp-silent.
    Silent,
    /// Every internal edge leaves a `Jump` (a chain the merged-chain
    /// quotient declined).
    Chain,
}

impl SegmentKind {
    fn name(self) -> &'static str {
        match self {
            Self::Diamond => "diamond",
            Self::Silent => "silent",
            Self::Chain => "chain",
        }
    }
}

/// One segment (see the module documentation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Segment {
    pub(super) head: Block,
    /// The laid-out machine block that lowers every member.
    pub(super) machine: Block,
    /// The head first, then the source's topological order.
    pub(super) members: Vec<Block>,
    /// Every `(s, z)`, `s` a member and `z` a successor of `s` outside the
    /// segment, in member order, then edge order (distinct targets of a
    /// `Switch`, [`switch_targets`]).
    pub(super) exits: Vec<(Block, Block)>,
    /// Every edge `(b, t)` between members, in the same order.
    pub(super) internal: Vec<(Block, Block)>,
    pub(super) kind: SegmentKind,
}

impl Segment {
    /// The distinct exit targets, in exit order.
    pub(super) fn targets(&self) -> Vec<Block> {
        let mut targets: Vec<Block> = Vec::new();
        for (_, target) in &self.exits {
            if !targets.contains(target) {
                targets.push(*target);
            }
        }
        targets
    }

    /// `h=[h, m1, ..]` in the stated ids.
    fn describe(&self) -> String {
        let members: Vec<String> = self.members.iter().map(|b| format!("{b:?}")).collect();
        format!("{:?}=[{}]", self.head, members.join(", "))
    }
}

/// The segments a correspondence is stated over, checked ([`check`]);
/// [`Self::none`] for every pair without one.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Segments {
    by_head: BTreeMap<Block, Segment>,
    head_of: BTreeMap<Block, Block>,
}

/// Slice 24c (OD-228): the segments a theorem is stated over, for the trace
/// line and the refusal suffix: how many, how many members other than their
/// heads, each one's kind, and their description in the stated ids.
#[derive(Debug, Clone)]
pub(super) struct SegmentsStated {
    pub(super) segments: usize,
    pub(super) members: usize,
    pub(super) kinds: Vec<SegmentKind>,
    pub(super) described: String,
}

impl SegmentsStated {
    /// `[diamond,silent]`.
    pub(super) fn kinds(&self) -> String {
        let kinds: Vec<&str> = self.kinds.iter().map(|kind| kind.name()).collect();
        format!("[{}]", kinds.join(","))
    }
}

impl Segments {
    pub(super) fn none() -> Self {
        Self::default()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.by_head.is_empty()
    }

    /// The segment `head` heads.
    pub(super) fn of_head(&self, head: Block) -> Option<&Segment> {
        self.by_head.get(&head)
    }

    /// The segment `block` is a member of (its head included).
    pub(super) fn of_member(&self, block: Block) -> Option<&Segment> {
        self.head_of
            .get(&block)
            .and_then(|head| self.by_head.get(head))
    }

    /// The segment `block` is a member of other than its head.
    pub(super) fn inner(&self, block: Block) -> Option<&Segment> {
        self.of_member(block)
            .filter(|segment| segment.head != block)
    }

    /// The segment machine block `machine` lowers.
    pub(super) fn of_machine(&self, machine: Block) -> Option<&Segment> {
        self.by_head
            .values()
            .find(|segment| segment.machine == machine)
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &Segment> {
        self.by_head.values()
    }

    /// `h=[h, m1, ..]; ..`.
    pub(super) fn describe(&self) -> String {
        self.iter()
            .map(Segment::describe)
            .collect::<Vec<_>>()
            .join("; ")
    }

    /// The trace record, `None` with no segment.
    pub(super) fn stated(&self) -> Option<SegmentsStated> {
        (!self.is_empty()).then(|| SegmentsStated {
            segments: self.by_head.len(),
            members: self.head_of.len() - self.by_head.len(),
            kinds: self.iter().map(|segment| segment.kind).collect(),
            described: self.describe(),
        })
    }

    /// A refusal of the route over these segments, as the owner reports it
    /// ([`over_segments`]); unchanged with no segment.
    pub(super) fn over(&self, refusal: X86BodyRefusal) -> X86BodyRefusal {
        if self.is_empty() {
            return refusal;
        }
        over_segments(&self.describe(), refusal)
    }
}

/// Slice 24c (OD-228): `refusal` of a route stated over the segments
/// `described` names: every `Unsupported` but the empty observable names
/// them ([`X86BodyUnsupported::OverSegments`], once, its reason's text first);
/// a mismatch is returned as it is.
pub(super) fn over_segments(described: &str, refusal: X86BodyRefusal) -> X86BodyRefusal {
    match refusal {
        X86BodyRefusal::Unsupported(reason)
            if !matches!(
                reason,
                X86BodyUnsupported::NoObservable | X86BodyUnsupported::OverSegments { .. }
            ) =>
        {
            X86BodyRefusal::Unsupported(X86BodyUnsupported::OverSegments {
                segments: described.to_owned(),
                reason: Box::new(reason),
            })
        }
        other => other,
    }
}

/// The chooser's result: the segments it proposes (unchecked) and, for each
/// machine block it declined, why, with the LIR blocks the decline concerns.
#[derive(Debug, Default)]
pub(super) struct Chosen {
    pub(super) segments: Vec<Segment>,
    pub(super) declined: BTreeMap<Block, String>,
    /// Each LIR block a declined candidate named or would have absorbed ->
    /// that candidate's machine block (the first in layout order).
    concerns: BTreeMap<Block, Block>,
}

impl Chosen {
    /// The decline that explains a correspondence refusal at `at`.
    fn note(&self, at: Failing) -> Option<&String> {
        at.machine
            .and_then(|machine| self.declined.get(&machine))
            .or_else(|| {
                at.lir
                    .and_then(|lir| self.concerns.get(&lir))
                    .and_then(|machine| self.declined.get(machine))
            })
    }
}

/// Where a correspondence refusal is: the machine block it names, or the LIR
/// block that has none.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct Failing {
    pub(super) machine: Option<Block>,
    pub(super) lir: Option<Block>,
}

/// The LIR terminator's name, for a refusal.
fn terminator(body: &trust_cg_lower::function::BasicBlock) -> &'static str {
    match body.instructions.last().map(|inst| &inst.opcode) {
        Some(L::Jump { .. }) => "Jump",
        Some(L::Brif { .. }) => "Brif",
        Some(L::Switch { .. }) => "Switch",
        Some(L::Return) => "Return",
        Some(L::Trap) => "Trap",
        _ => "non-terminator",
    }
}

/// Whether a LIR block ends in `Jump`, `Brif` or `Switch` (C5).
fn transfers(body: &trust_cg_lower::function::BasicBlock) -> bool {
    matches!(
        body.instructions.last().map(|inst| &inst.opcode),
        Some(L::Jump { .. } | L::Brif { .. } | L::Switch { .. })
    ) || mutated("s24c-member-any-terminator")
}

/// The LIR blocks machine block `block`'s rows name.
fn named_by(machine: &X86ISelFunction, block: Block) -> BTreeSet<Block> {
    machine
        .blocks
        .get(&block)
        .map(|body| {
            body.insts
                .iter()
                .filter_map(|inst| inst.lowering_provenance.source_id())
                .map(|id| Block(id.block))
                .collect()
        })
        .unwrap_or_default()
}

/// The distinct targets of a LIR block's terminator, in edge order.
fn targets_of(body: &trust_cg_lower::function::BasicBlock) -> Vec<Block> {
    let mut targets: Vec<Block> = Vec::new();
    for target in lir_successors(body) {
        if !targets.contains(&target) {
            targets.push(target);
        }
    }
    targets
}

/// The kind of a segment: [`SegmentKind`].
fn kind_of(source: &Function, members: &[Block], named: &BTreeSet<Block>) -> SegmentKind {
    let branches = members.iter().any(|member| {
        let body = &source.blocks[member];
        !matches!(
            body.instructions.last().map(|inst| &inst.opcode),
            Some(L::Jump { .. })
        ) && targets_of(body)
            .iter()
            .any(|target| members.contains(target))
    });
    if !branches {
        SegmentKind::Chain
    } else if named.len() == 1 {
        SegmentKind::Silent
    } else {
        SegmentKind::Diamond
    }
}

/// The segments the stamps propose (untrusted; see the module
/// documentation): each laid-out machine block, in layout order, but the
/// dispatch and search blocks, whose rows name two or more LIR blocks, or
/// name one some successor of which is stamp-silent (no row of any machine
/// block names it), is a candidate. Its head is the first block it names in
/// the topological order; each later block joins when it is named or
/// stamp-silent, live, not the entry nor a loop header, ends in a transfer
/// and has live predecessors, all members. A candidate is declined, with
/// why, when it names a block an earlier segment holds, when a named block
/// does not join, when nothing joins, or when the rule (C0-C7) refuses it.
pub(super) fn choose(source: &Function, machine: &X86ISelFunction, cfg: &SourceCfg) -> Chosen {
    let tables = dispatch_blocks(machine);
    let searched = search_blocks(source, machine, &cfg.dead, &tables);
    let headers: BTreeSet<Block> = cfg.loops.iter().map(|lp| lp.header).collect();
    let position: HashMap<Block, usize> = cfg
        .order
        .iter()
        .enumerate()
        .map(|(i, block)| (*block, i))
        .collect();
    let anywhere: BTreeSet<Block> = machine
        .blocks
        .values()
        .flat_map(|body| &body.insts)
        .filter_map(|inst| inst.lowering_provenance.source_id())
        .map(|id| Block(id.block))
        .collect();
    let live = |block: Block| source.blocks.contains_key(&block) && position.contains_key(&block);
    let silent = |block: Block| live(block) && !anywhere.contains(&block);
    let predecessors = |block: Block| -> Vec<Block> {
        if mutated("s24c-entering-any") {
            return Vec::new();
        }
        cfg.predecessors.get(&block).cloned().unwrap_or_default()
    };
    let mut chosen = Chosen::default();
    let mut claimed: BTreeMap<Block, (Block, Block)> = BTreeMap::new();
    for m in &machine.block_order {
        if tables.contains_key(m) || searched.contains_key(m) {
            continue;
        }
        let named = named_by(machine, *m);
        if named.is_empty() || named.iter().any(|lir| !source.blocks.contains_key(lir)) {
            continue;
        }
        let silent_successor = |block: Block| {
            cfg.successors
                .get(&block)
                .is_some_and(|targets| targets.iter().any(|target| silent(*target)))
        };
        let candidate = named.len() >= 2
            || named
                .iter()
                .next()
                .is_some_and(|only| silent_successor(*only));
        if !candidate {
            continue;
        }
        let decline = |chosen: &mut Chosen, note: String, concerns: &[Block]| {
            chosen.declined.insert(*m, note);
            for lir in concerns {
                chosen.concerns.entry(*lir).or_insert(*m);
            }
        };
        if let Some(dead) = named.iter().find(|lir| !live(**lir)) {
            decline(
                &mut chosen,
                format!("LIR block {dead:?}, which machine block {m:?} names, is unreachable"),
                &named.iter().copied().collect::<Vec<_>>(),
            );
            continue;
        }
        // A block an earlier segment already holds (N6).
        if let Some(taken) = named
            .iter()
            .filter(|lir| claimed.contains_key(lir) && !mutated("s24c-chooser-overlap"))
            .min_by_key(|lir| position[*lir])
        {
            let note = overlap(*taken, claimed[taken]);
            decline(
                &mut chosen,
                note,
                &named.iter().copied().collect::<Vec<_>>(),
            );
            continue;
        }
        let head = *named
            .iter()
            .min_by_key(|lir| position[*lir])
            .expect("a named block");
        let mut members = vec![head];
        let start = position[&head];
        for y in &cfg.order[start + 1..] {
            let y = *y;
            if !(named.contains(&y) || silent(y))
                || (claimed.contains_key(&y) && !mutated("s24c-chooser-overlap"))
                || y == source.entry_block
                || headers.contains(&y)
                || !transfers(&source.blocks[&y])
            {
                continue;
            }
            let from = predecessors(y);
            if (from.is_empty() && !mutated("s24c-entering-any"))
                || !from.iter().all(|p| members.contains(p))
            {
                continue;
            }
            members.push(y);
        }
        // The LIR blocks this candidate concerns: those it names and the
        // stamp-silent successors of its members.
        let mut concerns: Vec<Block> = named.iter().copied().collect();
        for member in &members {
            for target in cfg.successors.get(member).into_iter().flatten() {
                if silent(*target) && !concerns.contains(target) {
                    concerns.push(*target);
                }
            }
        }
        if let Some(missing) = named
            .iter()
            .filter(|lir| !members.contains(lir))
            .min_by_key(|lir| position[*lir])
        {
            let note = explain(
                source,
                cfg,
                &headers,
                (&members, head, *m),
                (*missing, true),
                &claimed,
            );
            decline(&mut chosen, note, &concerns);
            continue;
        }
        if members.len() == 1 {
            // The named block's stamp-silent successors could not join.
            let silent_target = cfg.successors[&head]
                .iter()
                .find(|target| silent(**target))
                .copied()
                .expect("a candidate");
            let note = explain(
                source,
                cfg,
                &headers,
                (&members, head, *m),
                (silent_target, false),
                &claimed,
            );
            decline(&mut chosen, note, &concerns);
            continue;
        }
        if let Some(why) = rule(
            source, machine, cfg, &tables, &searched, &headers, head, *m, &members,
        ) {
            decline(&mut chosen, why, &concerns);
            continue;
        }
        let (exits, internal) = edges_of(source, &members);
        for member in &members {
            claimed.insert(*member, (head, *m));
        }
        // Tests only: the head is the first member the rows do not name.
        let head = match members.iter().find(|member| !named.contains(member)) {
            Some(silent) if mutated("s24c-chooser-wrong-head") => *silent,
            _ => head,
        };
        chosen.segments.push(Segment {
            head,
            machine: *m,
            // Tests only, the neutral mutant: every segment labelled a
            // diamond (the kind is a label; no rule reads it).
            kind: if mutated("s24c-kind-diamond") {
                SegmentKind::Diamond
            } else {
                kind_of(source, &members, &named)
            },
            members,
            exits,
            internal,
        });
    }
    chosen
}

/// Why LIR block `missing`, which machine block `m` names (`named`), or a
/// stamp-silent successor of the head, does not join the segment of `head`
/// whose `members` joined (refusals N1 to N6 of the design's §3, in the order
/// N2, N3, N1, N5, N6, N4: a loop header is entered from its latch, so with
/// N1 first N3 would never be named).
fn explain(
    source: &Function,
    cfg: &SourceCfg,
    headers: &BTreeSet<Block>,
    (members, head, m): (&[Block], Block, Block),
    (missing, named): (Block, bool),
    claimed: &BTreeMap<Block, (Block, Block)>,
) -> String {
    let which = if named {
        format!("which machine block {m:?} names")
    } else {
        "which no machine block names".to_owned()
    };
    if missing == source.entry_block {
        return format!("LIR block {missing:?} is the entry block");
    }
    if headers.contains(&missing) {
        return format!("LIR block {missing:?} is a loop header");
    }
    let from = cfg.predecessors.get(&missing).cloned().unwrap_or_default();
    if let Some(outside) = from.iter().find(|p| !members.contains(p)) {
        let listed: Vec<String> = from.iter().map(|p| format!("{p:?}")).collect();
        return format!(
            "LIR block {missing:?}, {which}, is entered from [{}], and {outside:?} is not in the \
             segment of {head:?}",
            listed.join(", ")
        );
    }
    let body = &source.blocks[&missing];
    if !transfers(body) {
        return format!(
            "LIR block {missing:?} of the segment of {head:?} ends in a {}",
            terminator(body)
        );
    }
    if let Some(holder) = claimed.get(&missing) {
        return overlap(missing, *holder);
    }
    format!("LIR block {missing:?}, {which}, is not reached from {head:?} inside the segment")
}

/// Refusal N6: `block` is a member of the segment `(head, machine)` an
/// earlier machine block's stamps chose.
fn overlap(block: Block, (head, machine): (Block, Block)) -> String {
    format!("LIR block {block:?} is in the segment of {head:?} (machine block {machine:?})")
}

/// Source control-flow edges in member order, then edge order.
type SegmentEdges = Vec<(Block, Block)>;

/// The exits and the internal edges of `members` (member order, then edge
/// order, each distinct target once).
pub(super) fn edges_of(source: &Function, members: &[Block]) -> (SegmentEdges, SegmentEdges) {
    let mut exits = Vec::new();
    let mut internal = Vec::new();
    for member in members {
        for target in targets_of(&source.blocks[member]) {
            if members.contains(&target) {
                internal.push((*member, target));
            } else {
                exits.push((*member, target));
            }
        }
    }
    (exits, internal)
}

/// The chooser's own reading of C1, C3, C5, C6 and C7 for a candidate whose
/// members joined by the chooser's rule (refusals N5, N8, N9 and a member
/// branching back to the head); `None` when it holds.
#[allow(clippy::too_many_arguments)]
fn rule(
    source: &Function,
    machine: &X86ISelFunction,
    cfg: &SourceCfg,
    tables: &HashMap<Block, u32>,
    searched: &HashMap<Block, Block>,
    headers: &BTreeSet<Block>,
    head: Block,
    m: Block,
    members: &[Block],
) -> Option<String> {
    if !transfers(&source.blocks[&head]) {
        return Some(format!(
            "LIR block {head:?} of the segment of {head:?} ends in a {}",
            terminator(&source.blocks[&head])
        ));
    }
    for member in members {
        if cfg
            .successors
            .get(member)
            .is_some_and(|targets| targets.contains(&head))
        {
            return Some(format!(
                "LIR block {member:?} of the segment of {head:?} branches back to its head"
            ));
        }
    }
    for (_, target) in edges_of(source, members).0 {
        if headers.contains(&target) {
            return Some(format!(
                "the segment of {head:?} exits into loop header {target:?}"
            ));
        }
    }
    let reaches_table = machine.blocks[&m]
        .successors
        .iter()
        .any(|successor| tables.contains_key(successor) || searched.contains_key(successor))
        || machine.blocks[&m].insts.iter().any(|inst| {
            inst.operands
                .iter()
                .any(|operand| matches!(operand, O::JumpTableIndex(_)))
        });
    if reaches_table {
        return Some(format!(
            "the segment of {head:?} reaches a jump-table dispatch or binary-search block"
        ));
    }
    None
}

/// THE check of chosen segments (slice 24c's trusted code): it re-derives
/// C0 to C7 and the exits of each from the stated LIR `source`, its control
/// flow `cfg` (the loop headers and dead blocks) and the stamps of
/// `machine`, with its own live-predecessor map, and reuses nothing the
/// chooser computed. It runs in every build, before the segments are used;
/// a failure is the head and what fails.
///
/// Three clauses are implied by earlier ones for a `cfg` computed from
/// `source` and are kept as their own guards: the entry as a member (the
/// entry is first in the topological order, so the order clause refuses it
/// first), a member not reached from the head (with every live predecessor
/// of every member in `S` and the members in topological order, each member
/// is reached from the head), and a member branching to the head (the head
/// is then entered from a member, which C0 refuses first).
pub(super) fn check(
    source: &Function,
    machine: &X86ISelFunction,
    cfg: &SourceCfg,
    chosen: &[Segment],
) -> Result<Segments, (Block, String)> {
    let tables = dispatch_blocks(machine);
    let searched = search_blocks(source, machine, &cfg.dead, &tables);
    let headers: BTreeSet<Block> = cfg.loops.iter().map(|lp| lp.header).collect();
    let position: HashMap<Block, usize> = cfg
        .order
        .iter()
        .enumerate()
        .map(|(i, block)| (*block, i))
        .collect();
    let live = |block: &Block| source.blocks.contains_key(block) && !cfg.dead.contains(block);
    // Its own live-predecessor map, from every live block's terminator.
    let mut into: BTreeMap<Block, BTreeSet<Block>> = BTreeMap::new();
    let mut lir_blocks: Vec<&Block> = source.blocks.keys().collect();
    lir_blocks.sort_unstable();
    for block in lir_blocks {
        if !live(block) {
            continue;
        }
        for target in lir_successors(&source.blocks[block]) {
            into.entry(target).or_default().insert(*block);
        }
    }
    let mut segments = Segments::none();
    let mut machines: BTreeSet<Block> = BTreeSet::new();
    for segment in chosen {
        let head = segment.head;
        let fail = |detail: String| Err((head, detail));
        let Segment {
            head: _,
            machine: m,
            members,
            exits,
            internal: _,
            kind,
        } = segment;
        let in_s = |block: &Block| members.contains(block);
        // C1.
        if !live(&head) && !mutated("s24c-check-c1") {
            return fail(format!("its head {head:?} is not a live LIR block"));
        }
        if (!machine.block_order.contains(m) || tables.contains_key(m) || searched.contains_key(m))
            && !mutated("s24c-check-c1")
        {
            return fail(format!(
                "machine block {m:?} is not a laid-out block of its own"
            ));
        }
        // C0: the stamps.
        let named = named_by(machine, *m);
        if !named.contains(&head) {
            return fail(format!(
                "machine block {m:?} does not name its head {head:?}"
            ));
        }
        if let Some(outside) = named.iter().find(|lir| !in_s(lir))
            && !mutated("s24c-check-named")
        {
            return fail(format!(
                "machine block {m:?} names LIR block {outside:?}, which is not a member"
            ));
        }
        if let Some(bodiless) = named.iter().find(|lir| !source.blocks.contains_key(lir)) {
            return fail(format!("LIR block {bodiless:?} has no body"));
        }
        if !machines.insert(*m) && !mutated("s24c-check-shared") {
            return fail(format!("machine block {m:?} lowers two segments"));
        }
        if let Some(other) = members
            .iter()
            .find_map(|member| segments.of_member(*member).map(|s| (*member, s.head)))
            && !mutated("s24c-check-overlap")
        {
            return fail(format!(
                "LIR block {:?} is also in the segment of {:?}",
                other.0, other.1
            ));
        }
        if let Some(inside) = into
            .get(&head)
            .and_then(|from| from.iter().find(|from| in_s(from)))
            && !mutated("s24c-check-head-entry")
        {
            return fail(format!("its head is entered from member {inside:?}"));
        }
        // The members: the head first, distinct, in the topological order.
        if members.first() != Some(&head) || members.len() < 2 {
            return fail("its members do not start at its head".into());
        }
        for pair in members.windows(2) {
            match (position.get(&pair[0]), position.get(&pair[1])) {
                (Some(a), Some(b)) if a < b => {}
                _ if mutated("s24c-check-order") => {}
                _ => {
                    return fail(format!(
                        "its members {:?} and {:?} are not live and in topological order",
                        pair[0], pair[1]
                    ));
                }
            }
        }
        // C2.
        for member in &members[1..] {
            if *member == source.entry_block {
                return fail(format!("member {member:?} is the entry block"));
            }
            let from = into.get(member).cloned().unwrap_or_default();
            if from.is_empty() {
                return fail(format!("member {member:?} has no live predecessor"));
            }
            if let Some(outside) = from.iter().find(|from| !in_s(from))
                && !mutated("s24c-check-entering-any")
            {
                return fail(format!(
                    "member {member:?} is entered from {outside:?}, outside the segment"
                ));
            }
        }
        let mut reached: BTreeSet<Block> = BTreeSet::from([head]);
        let mut work = vec![head];
        while let Some(block) = work.pop() {
            for target in lir_successors(&source.blocks[&block]) {
                if in_s(&target) && reached.insert(target) {
                    work.push(target);
                }
            }
        }
        if let Some(unreached) = members.iter().find(|member| !reached.contains(member)) {
            return fail(format!(
                "member {unreached:?} is not reached from the head inside the segment"
            ));
        }
        // C3 and C5.
        for member in members {
            let body = &source.blocks[member];
            if !transfers(body) && !mutated("s24c-check-terminator") {
                return fail(format!("member {member:?} ends in a {}", terminator(body)));
            }
            for target in lir_successors(body) {
                if target == head {
                    return fail(format!("member {member:?} branches to the head"));
                }
                if in_s(&target)
                    && position.get(member) >= position.get(&target)
                    && !mutated("s24c-check-backward")
                {
                    return fail(format!("the edge {member:?} -> {target:?} runs backward"));
                }
            }
        }
        // The exits, re-derived; C6.
        let mut derived: Vec<(Block, Block)> = Vec::new();
        let mut internal: Vec<(Block, Block)> = Vec::new();
        for member in members {
            let mut seen: Vec<Block> = Vec::new();
            for target in lir_successors(&source.blocks[member]) {
                if seen.contains(&target) {
                    continue;
                }
                seen.push(target);
                if in_s(&target) {
                    internal.push((*member, target));
                } else {
                    derived.push((*member, target));
                }
            }
        }
        if derived != *exits && !mutated("s24c-check-exits") {
            return fail("its exits are not its members' edges out of it".into());
        }
        if let Some((_, header)) = exits.iter().find(|(_, target)| headers.contains(target))
            && !mutated("s24c-check-loop-exit")
        {
            return fail(format!("it exits into loop header {header:?}"));
        }
        // C7.
        let Some(body) = machine.blocks.get(m) else {
            return fail(format!("machine block {m:?} has no rows"));
        };
        if (body
            .successors
            .iter()
            .any(|successor| tables.contains_key(successor) || searched.contains_key(successor))
            || body.insts.iter().any(|inst| {
                inst.operands
                    .iter()
                    .any(|operand| matches!(operand, O::JumpTableIndex(_)))
            }))
            && !mutated("s24c-check-dispatch")
        {
            return fail(format!(
                "machine block {m:?} reaches a jump-table dispatch or binary-search block"
            ));
        }
        for member in members {
            segments.head_of.insert(*member, head);
        }
        segments.by_head.insert(
            head,
            Segment {
                head,
                machine: *m,
                members: members.clone(),
                exits: exits.clone(),
                internal,
                kind: *kind,
            },
        );
    }
    Ok(segments)
}

/// The block correspondence of the stated pair over the segments the stamps
/// choose, for a pair whose one-to-one correspondence failed with `reason`:
/// [`choose`], [`check`] (a failure is `Construction`, never credit), then
/// [`block_correspondence_over`]. With no candidate the refusal is `reason`
/// as `quotient` annotates it, byte for byte; otherwise a refusal names,
/// after its own text, slice 24a's decline of its machine block (only when it
/// is the block [`quotient::Quotient::first_note_at`] names, so a note never
/// describes another block) and the chooser's decline of the block it
/// concerns (`; no segment: ...`).
pub(super) fn correspondence(
    source: &Function,
    machine: &X86ISelFunction,
    cfg: &SourceCfg,
    reason: String,
    quotient: Option<&quotient::Quotient<'_>>,
) -> Result<Result<Correspondence, String>, X86BodyRefusal> {
    let annotate = |reason: String| match quotient {
        Some(quotient) => quotient.annotate(reason),
        None => reason,
    };
    let chosen = choose(source, machine, cfg);
    if chosen.segments.is_empty() && chosen.declined.is_empty() {
        return Ok(Err(annotate(reason)));
    }
    let segments = if chosen.segments.is_empty() {
        Segments::none()
    } else if mutated("s24c-check-off") {
        // Tests only: the chooser's segments, unchecked.
        let mut unchecked = Segments::none();
        for segment in &chosen.segments {
            for member in &segment.members {
                unchecked.head_of.insert(*member, segment.head);
            }
            unchecked.by_head.insert(segment.head, segment.clone());
        }
        unchecked
    } else {
        check(source, machine, cfg, &chosen.segments).map_err(|(head, detail)| {
            unsupported(X86BodyUnsupported::Construction(format!(
                "the segment of {head:?} is not single-entry: {detail}"
            )))
        })?
    };
    match block_correspondence_over(source, machine, &cfg.dead, &segments) {
        Ok(correspondence) => Ok(Ok(correspondence)),
        Err((text, at)) => {
            let first_note_at = quotient.and_then(|quotient| quotient.first_note_at());
            let mut text = if at.machine.is_some() && at.machine == first_note_at {
                annotate(text)
            } else {
                text
            };
            if let Some(note) = chosen.note(at) {
                text.push_str("; no segment: ");
                text.push_str(note);
            }
            Ok(Err(text))
        }
    }
}

/// [`correspondence`] in place: a skeleton whose correspondence failed gets
/// the one over segments, or keeps a refusal that names why there is none.
/// `source` and `flow` are the pair's stated LIR and its control flow.
pub(super) fn restate(
    cfg: &mut MachineCfg<'_>,
    source: &Function,
    flow: &SourceCfg,
    quotient: Option<&quotient::Quotient<'_>>,
) -> Result<(), X86BodyRefusal> {
    if let Err(reason) = &cfg.correspondence {
        let reason = reason.clone();
        cfg.correspondence = correspondence(source, cfg.machine, flow, reason, quotient)?;
    }
    Ok(())
}

/// Whether a unit (a DAG block's fragment) carries an EFFECT: a call, an
/// incoming access, a rounding operation (its events), a stop or an indexed
/// access.
fn carries(program: &SourceProgram) -> bool {
    !program.events.is_empty() || !program.stops.is_empty() || !program.indexed.is_empty()
}

/// The LIR blocks whose effects a path's program carries: its calls,
/// incoming accesses, rounding operations, stops and indexed accesses.
fn effect_blocks(program: &SourceProgram) -> BTreeSet<Block> {
    program
        .calls
        .iter()
        .map(|call| call.block)
        .chain(program.accesses.iter().map(|access| access.block))
        .chain(program.floats.iter().map(|float| float.block))
        .chain(program.stops.iter().map(|stop| stop.block))
        .chain(program.indexed.iter().map(|site| site.block))
        .collect()
}

/// C9, the effects rule (trusted, every build): the member `E` whose program
/// the segment's machine block is walked against. At most one member carries
/// an effect (`carries`), and it dominates, inside the segment, every member
/// an exit leaves; with none, `E` is the head. So every run through the
/// segment passes `E`, and the one walk of the machine block, which runs its
/// rows on every path, meets each source event of the segment in order
/// (refusals N10, N11).
fn effect_member(
    segment: &Segment,
    carries: impl Fn(Block) -> bool,
) -> Result<Block, X86BodyRefusal> {
    let head = segment.head;
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    if mutated("s24c-effects-off") {
        return Ok(head);
    }
    let carriers: Vec<Block> = segment
        .members
        .iter()
        .copied()
        .filter(|member| carries(*member))
        .collect();
    let effect = match carriers.as_slice() {
        [] => return Ok(head),
        [only] => *only,
        [first, ..] if mutated("s24c-two-effect-members") => *first,
        [first, second, ..] => {
            return Err(no_claim(format!(
                "LIR blocks {first:?} and {second:?} in the segment of {head:?} both have calls, \
                 accesses, rounding operations, stops or indexed accesses"
            )));
        }
    };
    if effect == head || mutated("s24c-effect-off-spine") {
        return Ok(effect);
    }
    // `effect` dominates every exit's source when none is reached from the
    // head along internal edges that avoid it.
    let mut reached: BTreeSet<Block> = BTreeSet::from([head]);
    let mut work = vec![head];
    while let Some(block) = work.pop() {
        for (_, target) in segment.internal.iter().filter(|(from, _)| *from == block) {
            if *target != effect && reached.insert(*target) {
                work.push(*target);
            }
        }
    }
    if segment.exits.iter().any(|(from, _)| reached.contains(from)) {
        return Err(no_claim(format!(
            "LIR block {effect:?} in the segment of {head:?} has a call, incoming access, \
             rounding operation, stop or indexed access, and a run through the segment need not \
             pass it (machine block {:?} runs its rows on every path)",
            segment.machine
        )));
    }
    Ok(effect)
}

/// C9 on one source path (slice 6's encoding): for each segment the path
/// enters, the effects rule over the members whose effects the path's
/// program carries. Every live block is on some path, so the paths together
/// check the rule of each segment.
pub(super) fn path_effects(
    segments: &Segments,
    program: &SourceProgram,
) -> Result<(), X86BodyRefusal> {
    let carried = effect_blocks(program);
    for segment in segments.iter() {
        if program.blocks.contains(&segment.head) {
            effect_member(segment, |member| carried.contains(&member))?;
        }
    }
    Ok(())
}

/// C10: no internal join of the segment (a member other than its head with
/// several predecessors) has a private byte OD-192 leaves dead
/// ([`DagBody::join_dead`]): the machine block merges no state there, so the
/// bytes would stay readable on its side (refusal N12).
pub(super) fn internal_joins(segment: &Segment, dag: &DagBody) -> Result<(), X86BodyRefusal> {
    for member in &segment.members[1..] {
        if dag
            .predecessors
            .get(member)
            .is_some_and(|from| from.len() > 1)
            && dag.join_dead.contains_key(member)
        {
            return Err(unsupported(X86BodyUnsupported::MachineFunction(format!(
                "the segment of {:?} has an internal join {member:?} whose private bytes OD-192 \
                 leaves dead",
                segment.head
            ))));
        }
    }
    Ok(())
}

impl Walked {
    /// Slice 24c: the walk of a segment member that is not its effect member
    /// ([`walk_head`]): no rows, no items, nothing stopped.
    fn member() -> Self {
        Self {
            entry_names: Vec::new(),
            abi_views: Vec::new(),
            returns: Vec::new(),
            return_affine: Vec::new(),
            calls: Vec::new(),
            accesses: Vec::new(),
            floats: Vec::new(),
            literals: Vec::new(),
            bound_rows: Vec::new(),
            end_stop: (bit_zero(), bit_zero()),
            indexed: Vec::new(),
        }
    }

    /// Whether the walk ran a row or claims an item.
    fn ran(&self) -> bool {
        !(self.returns.is_empty()
            && self.calls.is_empty()
            && self.accesses.is_empty()
            && self.floats.is_empty()
            && self.literals.is_empty()
            && self.bound_rows.is_empty()
            && self.indexed.is_empty())
    }
}

/// The walk of a segment in a DAG ([`walk_region`]), at its head, from the
/// head's entry state `entry`: C9 picks the effect member `E` and C10 holds;
/// then, for each distinct exit target `z`, every route of the segment's
/// machine block to `z`'s ([`block_routes`]) is walked against `E`'s program
/// ([`walk_routes`]). Each exit `(s, z)` gets that walk's `jcc` literals and
/// end state; each internal edge no literal (it is no machine transfer). `E`
/// keeps the walk (the first target's, with every target's bound rows and
/// in-bounds claims), every other member [`Walked::member`]. Every target's
/// walk must stop as the first does (the slice-14 stop rule).
#[allow(clippy::too_many_arguments)]
pub(super) fn walk_head(
    segment: &Segment,
    dag: &DagBody,
    sites: &SourceSites,
    cfg: &MachineCfg<'_>,
    correspondence: &Correspondence,
    names: &mut MachineNames,
    frame_bytes: &mut Vec<FrameAddr>,
    entry: &MachineState,
    blocks: &mut HashMap<Block, Walked>,
    edges: &mut HashMap<(Block, Block), Vec<E>>,
    exits: &mut HashMap<(Block, Block), MachineState>,
) -> Result<(), X86BodyRefusal> {
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    let effect = effect_member(segment, |member| {
        dag.blocks.get(&member).is_some_and(carries)
    })?;
    internal_joins(segment, dag)?;
    let program = dag.blocks.get(&effect).ok_or_else(|| {
        unsupported(X86BodyUnsupported::Construction(format!(
            "segment member {effect:?} has no fragment"
        )))
    })?;
    let consts = cfg.machine;
    let mut first: Option<Walked> = None;
    for target in segment.targets() {
        let to = correspondence
            .lowering
            .get(&target)
            .copied()
            .ok_or_else(|| no_claim(format!("the source block {target:?} has no machine block")))?;
        let routes = block_routes(cfg, correspondence, segment.machine, to)?;
        let (walked, state) =
            walk_routes(program, sites, &routes, names, frame_bytes, consts, entry)?;
        for (from, _) in segment.exits.iter().filter(|(_, to)| *to == target) {
            edges.insert((*from, target), walked.literals.clone());
            exits.insert((*from, target), state.clone());
        }
        let Some(earliest) = first.as_mut() else {
            first = Some(walked);
            continue;
        };
        if walked.end_stop != earliest.end_stop {
            return Err(no_claim(format!(
                "the machine block that lowers block {:?} stops differently on its edges",
                segment.head
            )));
        }
        earliest.bound_rows.extend(walked.bound_rows);
        for claim in walked.indexed {
            if !earliest.indexed.contains(&claim) {
                earliest.indexed.push(claim);
            }
        }
    }
    let mut walked = first.ok_or_else(|| {
        unsupported(X86BodyUnsupported::Construction(format!(
            "the segment of {:?} has no exit",
            segment.head
        )))
    })?;
    walked.bound_rows.sort_unstable();
    walked.bound_rows.dedup();
    for edge in &segment.internal {
        edges.insert(*edge, Vec::new());
    }
    // Tests only: the walk kept by the segment's last member instead of `E`
    // (the member guard re-derives `E` and refuses it).
    let keeper = match segment.members.last() {
        Some(last) if mutated("s24c-walk-on-member") => *last,
        _ => effect,
    };
    for member in &segment.members {
        if *member == keeper {
            continue;
        }
        let walk = match dag.blocks.get(member) {
            // Tests only: a member walked as if it had a machine block of its
            // own, the segment's.
            Some(own) if mutated("s24c-member-rewalk") => {
                let target = segment.targets()[0];
                let routes = block_routes(
                    cfg,
                    correspondence,
                    segment.machine,
                    correspondence.lowering[&target],
                )?;
                walk_routes(own, sites, &routes, names, frame_bytes, consts, entry)?.0
            }
            _ => Walked::member(),
        };
        blocks.insert(*member, walk);
    }
    blocks.insert(keeper, walked);
    Ok(())
}

/// Each segment whose head is a block of `dag`, for the member guard
/// ([`guard_members`]).
pub(super) fn in_dag(segments: &Segments, dag: &DagBody) -> Vec<Segment> {
    segments
        .iter()
        .filter(|segment| dag.blocks.contains_key(&segment.head))
        .cloned()
        .collect()
}

/// C11, the member guard where the theorem consumes the walks (trusted, every
/// build): of a segment's members in a DAG, every unit ends in `Jump`,
/// `Brif` or `Switch` and returns nothing; the effect member `E` is
/// re-derived from the units' own programs ([`effect_member`]) and only `E`
/// may have a walk (the theorem states each unit's stop claims, in-bounds
/// claims and items under that unit's own guard, so a walk on another member
/// would state them under a guard that some runs through the segment do not
/// satisfy); and a unit whose walk is empty has no call, access, rounding
/// operation, stop or indexed access, so no source event of the segment is
/// left unpaired by the consumers that zip a unit's events with its walk.
pub(super) fn guard_members(
    segment: &Segment,
    dag: &DagBody,
    dag_walks: &DagWalks,
) -> Result<(), X86BodyRefusal> {
    if mutated("s24c-theorem-guard-off") {
        return Ok(());
    }
    let construction = |member: Block, what: &str| {
        Err(unsupported(X86BodyUnsupported::Construction(format!(
            "segment member {member:?} carries {what}"
        ))))
    };
    let members = &segment.members;
    for member in members {
        if !dag.blocks.contains_key(member) || !dag_walks.blocks.contains_key(member) {
            return construction(*member, "no unit");
        }
    }
    let effect =
        effect_member(segment, |member| carries(&dag.blocks[&member])).map_err(|refusal| {
            unsupported(X86BodyUnsupported::Construction(format!(
                "the effects rule refuses the segment of {:?} where the theorem consumes its \
                 walks: {refusal}",
                segment.head
            )))
        })?;
    // Tests only: the rule as slice 24c first stated it (at most one member
    // walks, whichever it is), the fails-before record of re-deriving `E`.
    let mut walker: Option<Block> = None;
    for member in members {
        let (Some(program), Some(walks)) = (dag.blocks.get(member), dag_walks.blocks.get(member))
        else {
            return construction(*member, "no unit");
        };
        if program.end != SourceEnd::Continue || !program.returned.is_empty() {
            return construction(*member, "a return or a trap");
        }
        let ran = std::iter::once(&walks.psabi)
            .chain(walks.clean.as_ref())
            .any(Walked::ran);
        if ran && mutated("s24c-guard-one-walker") {
            if let Some(first) = walker {
                return construction(*member, &format!("a walk besides member {first:?}'s"));
            }
            walker = Some(*member);
        } else if ran {
            if *member != effect {
                return construction(
                    *member,
                    &format!("a walk, and the effects rule picks member {effect:?}"),
                );
            }
        } else if carries(program) {
            return construction(
                *member,
                "a call, access, rounding operation, stop or indexed access and no walk",
            );
        }
    }
    Ok(())
}

/// Why [`bans`] bans a cut point, with the head of the segment it concerns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Ban {
    /// A point of a member other than the head, or inside the head: the
    /// segment states it inside its machine block.
    Inside(Block),
    /// The start of an exit target that declares parameters: their copies
    /// run inside the segment's machine block.
    ExitParameters(Block),
    /// A point where a value is live whose every LIR definition is in a
    /// member other than the head (a join's parameter, whose copies are the
    /// members' edge copies, or a value a dominating member defines).
    Defined(Block, Value),
}

impl Ban {
    fn head(self) -> Block {
        match self {
            Self::Inside(head) | Self::ExitParameters(head) | Self::Defined(head, _) => head,
        }
    }
}

/// Slice 16 with segments: the cut points a plan may not choose and a test
/// policy may not name, each with why ([`Ban`]): every point of a member
/// other than the head, every point inside the head, the start of every
/// exit target that declares parameters, and every other point where a value
/// is live whose every definition is in a member other than a head. A cut's
/// pairing reads `lowering` ([`split::cut_pairing`]), which names no machine
/// block for a member, so a cut at any of these points pairs nothing; `cfg`
/// is `source`'s control flow.
pub(super) fn bans(
    source: &Function,
    cfg: &SourceCfg,
    segments: &Segments,
) -> BTreeMap<(Block, usize), Ban> {
    let mut banned = BTreeMap::new();
    if mutated("s24c-parts-no-ban") || segments.is_empty() {
        return banned;
    }
    for segment in segments.iter() {
        for member in &segment.members {
            let length = source.blocks[member].instructions.len();
            let first = usize::from(*member == segment.head);
            for index in first..=length {
                banned.insert((*member, index), Ban::Inside(segment.head));
            }
        }
        for target in segment.targets() {
            if source
                .blocks
                .get(&target)
                .is_some_and(|body| !body.params.is_empty())
            {
                banned
                    .entry((target, 0))
                    .or_insert(Ban::ExitParameters(segment.head));
            }
        }
    }
    if mutated("s24c-parts-defined-no-ban") {
        return banned;
    }
    // Every value whose every definition is in a member other than a head,
    // with that member's head.
    let mut definitions: HashMap<Value, Vec<Block>> = HashMap::new();
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort_unstable();
    for block in blocks {
        for inst in &source.blocks[block].instructions {
            for result in &inst.results {
                definitions.entry(*result).or_default().push(*block);
            }
        }
    }
    let inner: HashMap<Value, Block> = definitions
        .iter()
        .filter_map(|(value, at)| {
            let head = segments.inner(*at.first()?)?.head;
            at.iter()
                .all(|block| segments.inner(*block).is_some())
                .then_some((*value, head))
        })
        .collect();
    if inner.is_empty() {
        return banned;
    }
    let live = split::live_in(source, cfg);
    for block in &cfg.order {
        if segments.inner(*block).is_some() {
            continue;
        }
        let body = &source.blocks[block];
        let mut current: std::collections::HashSet<Value> = std::collections::HashSet::new();
        for target in &cfg.successors[block] {
            current.extend(live[target].iter().copied());
        }
        for index in (0..body.instructions.len()).rev() {
            let inst = &body.instructions[index];
            for result in &inst.results {
                current.remove(result);
            }
            current.extend(inst.args.iter().copied());
            if let Some((value, head)) = current
                .iter()
                .filter_map(|value| inner.get(value).map(|head| (*value, *head)))
                .min_by_key(|(value, _)| value.0)
            {
                banned
                    .entry((*block, index))
                    .or_insert(Ban::Defined(head, value));
            }
        }
    }
    banned
}

/// Refusal N13: a test policy's cut point at a point [`bans`] names.
pub(super) fn banned_point(
    segments: &Segments,
    banned: &BTreeMap<(Block, usize), Ban>,
    point: (Block, usize),
) -> Option<X86BodyRefusal> {
    let ban = banned.get(&point)?;
    let head = ban.head();
    let machine = segments.of_head(head)?.machine;
    let (block, index) = point;
    let text = match ban {
        Ban::Inside(_) => format!(
            "a cut point in LIR block {block:?}, which the segment of {head:?} states inside \
             machine block {machine:?}"
        ),
        Ban::ExitParameters(_) => format!(
            "a cut point at the start of LIR block {block:?}, an exit target of the segment of \
             {head:?} whose parameters machine block {machine:?} copies"
        ),
        Ban::Defined(_, value) => format!(
            "a cut point at instruction {index} of LIR block {block:?}, where {value:?} is live, \
             which only members of the segment of {head:?} define (inside machine block \
             {machine:?})"
        ),
    };
    Some(unsupported(X86BodyUnsupported::MachineFunction(text)))
}
