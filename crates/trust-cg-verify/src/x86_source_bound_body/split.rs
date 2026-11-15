// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 16: a source past the single-query bounds, stated as one theorem
//! replayed in parts (ruling OD-182 in `docs/decision-record.md`).
//!
//! A function whose LIR has more than [`MAX_BODY_BLOCKS`] blocks or
//! [`MAX_BODY_INSTRUCTIONS`] instructions, or whose pre-RA stream has more
//! than [`MAX_MACHINE_BLOCKS`] blocks or [`MAX_MACHINE_ROWS`] rows, is CUT:
//! at its entry, at every loop header, and at the program points a
//! deterministic plan chooses ([`plan_points`]): block starts, and clean
//! instruction boundaries inside straight-line blocks. Every other function
//! keeps the theorem of slices 1 to 15 byte for byte: the choice depends on
//! the function's shape alone ([`fits_one_query`]), never on a replay.
//!
//! *Pieces.* A cut inside block `B` before its instruction `k` splits `B` into
//! two blocks, on the LIR and on the machine side ([`rewrite_pieces`]): the
//! LIR block keeps instructions `0..k` and ends in a `Jump` to a new block
//! holding the rest; the machine block that lowers `B` keeps the rows its
//! TV-1 stamps attribute to instructions before `k` and falls through to a
//! new block, laid out right after it, holding the rest. The rewritten
//! machine stream is the original's rows in the original order, so every row
//! keeps its walk ordinal (checked). A point is admitted only at a clean
//! stamp boundary: every row before the split row is stamped with an
//! instruction before `k` or unstamped, every row from it on with `k` or
//! later or unstamped, and no physical register, flag or outgoing argument
//! area is live there ([`clean_split_row`]).
//!
//! *Regions.* The region of a cut point is every block a run reaches from it
//! before it reaches a cut point again (slice 12's [`source_regions`] over
//! the pieces): a DAG, stated with slice 9's machinery.
//!
//! *The cut interface* ([`CutInterface`]). At every cut point `C` but the
//! entry, every live LIR value (and every parameter of `C`) and every private
//! byte some edge into `C` wrote is an ITEM of `C`'s interface, unless it is
//! CLOSED: a constant (an `Iconst`), a parameter of the function, a symbol's
//! address, a private address, or a byte stored from such a constant or
//! parameter, or of an aggregate parameter's register, or holding a stored
//! private address; each is fixed for the run and is carried exactly, and
//! checked to be the same on every edge into `C`. A value item is one free
//! input `x{C}v{i}` shared by both sides; its machine register is the one the
//! last row stamped with the value's definition writes (for a parameter of
//! `C`, the row stamped with its copy on an edge into `C`), whose low bits
//! hold it ([`ParamRoot`]); a byte item is one free input `x{C}b{s}o{o}` on
//! both sides. On EVERY edge into `C` the theorem states each item's source
//! term equal to the machine's ([`split_relation`]): the value against the
//! low bits of its register, the byte against the machine's byte at the same
//! frame address. Every other machine register starts as the term every
//! edge into `C` leaves in it when that term is a function of the run's fixed
//! inputs alone (an entry register, a symbol, a constant), else
//! [`RegValue::Carried`] (a read makes no claim); the flags start
//! unmodelled; no outgoing argument area may be open.
//!
//! *Defined inputs* (ruling OD-233). A value item (not `I128`) or byte item
//! that no edge taints is DEFINED when its source term on EVERY edge into
//! `C` (forward and back) resolves to one term `T` over the run's fixed
//! inputs: with the statement's definitions and the other defined inputs
//! inlined, normalized by the bit identities and the exact fold of the
//! parts' spelling, naming only entry registers and incoming stack
//! eightbytes, parameter bindings, symbol addresses, frame bytes' initial
//! values and `bool` caller views (no slot address), of at most
//! [`MAX_CLOSED_TERM_NODES`] nodes ([`run_fixed_term`]). Its name is then
//! no free input: the statement defines it as `T`, right after the caller
//! views, and on every edge into `C`, in that edge's part, under the edge's
//! guard and where the source runs, claims the input's source term equal to
//! the name (a claim that is no observable; an unchanged input on a back
//! edge is the name itself and states nothing). Nothing else about the
//! interface, the pairing, the machine walk or the relation changes. The
//! choice ([`cut_definitions`]: seed from the forward edges in region
//! order, then drop what some edge does not bring) reads the source terms
//! alone and is untrusted: `build_theorem` refuses a defined term that
//! names anything not fixed for the run, and an edge that does not carry a
//! defined input's claim, and a wrong term is refuted by its edge's claim.
//!
//! *Parts.* Each region's claims (its observed items under its guards, its
//! edges' `jcc` literals, and the relation on each of its cut edges) mention
//! only its own definitions and the run's fixed inputs, so each region is
//! one closed PART ([`split_parts`]): the cone of definitions its claims
//! reach, one AY query and one Clean check. The function's theorem is the
//! conjunction of the parts ([`SourceBoundX86Body::obligation`], never
//! replayed itself); every row is credited only when every part replays
//! Valid, and the part inventory is checked against that statement at credit
//! and at export ([`check_x86_body_parts`]).
//!
//! *The merged-chain quotient* (slice 24a, ruling OD-226). A pair whose
//! machine blocks do not correspond one to one with its LIR blocks is
//! planned, cut and stated over its merged-chain quotient
//! ([`super::quotient`]) when the stamps choose a chain to contract; the
//! bounds above, the frame, the control flow and the entry parameters of the
//! ORIGINAL source are checked first, then the quotient's. A test policy's
//! points are the original's, mapped into the quotient (a point at a `Jump`
//! the quotient removes refuses); the plan, the pieces and the regions are
//! the quotient's, every new piece's id above every block id of the original
//! pair; every audit coordinate is mapped back through the pieces
//! ([`Pieces::original`]), then the quotient. The regions admitted are
//! pieces of the quotient, exactly as they are pieces of the source without
//! it; the quotient admits exactly what its pieces state, which can be more
//! than the original's own region admission would (flags across the old
//! seam, a header copy found in the merged block, a join's edge-copy run
//! measured over the merged block): exact, never wider in meaning.

use super::*;
use trust_cg_lower::instructions::Instruction;

/// The machine rows a region of a function stated in parts may have (slice
/// 16), and its LIR instructions and blocks: the bounds of one part's query.
pub(super) const MAX_REGION_ROWS: usize = 256;
pub(super) const MAX_REGION_INSTRUCTIONS: usize = MAX_BODY_INSTRUCTIONS;
pub(super) const MAX_REGION_BLOCKS: usize = MAX_BODY_BLOCKS;

/// The most parts, and the most machine rows, LIR instructions and blocks, of
/// a function stated in parts (slice 16).
pub(super) const MAX_PARTS: usize = 32;
pub(super) const MAX_SPLIT_ROWS: usize = 8192;
pub(super) const MAX_SPLIT_INSTRUCTIONS: usize = 8192;
pub(super) const MAX_SPLIT_BLOCKS: usize = 1024;

/// What part `k` of `n` of a function's theorem is named: the theorem's name,
/// this separator, `part {k} of {n}`.
/// The most planned cut points banned and planned around in one function
/// ([`source_bound_split`]).
const MAX_REPLANS: usize = 4;

pub const X86_BODY_PART_SEPARATOR: &str = " | ";

/// Whether `name` names a part of an x86-64 body theorem stated in parts.
pub fn is_x86_body_part_name(name: &str) -> bool {
    name.strip_prefix(X86_BODY_OBLIGATION_NAME)
        .and_then(|rest| rest.strip_prefix(X86_BODY_PART_SEPARATOR))
        .is_some_and(|rest| rest.starts_with("part "))
}

/// Slice 19 (OD-197): whether `name` names one claim of an x86-64 body
/// theorem or of one of its parts, replayed claim by claim
/// ([`claim_parts`]).
pub fn is_x86_body_claim_name(name: &str) -> bool {
    name.starts_with(X86_BODY_OBLIGATION_NAME) && name.contains(X86_BODY_CLAIM_SEPARATOR)
}

/// The bounds and cut choice of a function stated in parts.
#[derive(Debug, Clone)]
pub(crate) struct SplitPolicy {
    pub(crate) region_rows: usize,
    pub(crate) region_instructions: usize,
    pub(crate) region_blocks: usize,
    pub(crate) max_parts: usize,
    /// Tests only: cut exactly at these program points `(block, index)` (an
    /// index of 0 is the block's start), besides the entry and the loop
    /// headers, instead of the planner's choice; and state the function in
    /// parts whatever its size.
    pub(crate) points: Option<Vec<(Block, usize)>>,
}

impl SplitPolicy {
    pub(crate) const PRODUCTION: Self = Self {
        region_rows: MAX_REGION_ROWS,
        region_instructions: MAX_REGION_INSTRUCTIONS,
        region_blocks: MAX_REGION_BLOCKS,
        max_parts: MAX_PARTS,
        points: None,
    };
}

/// Whether the single-query theorem of slices 1 to 15 states `source` and
/// `machine` (within its bounds); any other pair is stated in parts.
pub(super) fn fits_one_query(source: &Function, machine: &X86ISelFunction) -> bool {
    let instructions: usize = source
        .blocks
        .values()
        .map(|block| block.instructions.len())
        .sum();
    let rows: usize = machine.blocks.values().map(|block| block.insts.len()).sum();
    source.blocks.len() <= MAX_BODY_BLOCKS
        && instructions <= MAX_BODY_INSTRUCTIONS
        && machine.blocks.len() <= MAX_MACHINE_BLOCKS
        && rows <= MAX_MACHINE_ROWS
}

/// Whether a source past the single-query LIR bounds could be stated in
/// parts: within a split body's bounds and admitted as one body when its size
/// is ignored. An over-approximation (the split admission only generalizes
/// more) for deciding whether the body owner applies; a source within the
/// LIR bounds is decided by [`admitted_body`] alone.
pub(super) fn source_admits_split(source: &Function) -> bool {
    let instructions: usize = source
        .blocks
        .values()
        .map(|block| block.instructions.len())
        .sum();
    (source.blocks.len() > MAX_BODY_BLOCKS || instructions > MAX_BODY_INSTRUCTIONS)
        && source.blocks.len() <= MAX_SPLIT_BLOCKS
        && instructions <= MAX_SPLIT_INSTRUCTIONS
        && admitted_body_bounded(source, None, MAX_SPLIT_BLOCKS, MAX_SPLIT_INSTRUCTIONS).is_ok()
}

/// Whether the owner may state `source` and `machine` in parts: the checks
/// [`source_bound_split`] makes before it plans its cut points (both within
/// the bounds of a function stated in parts, the frame, the control flow at
/// those bounds, the entry parameters, one function named on both sides).
/// `false` means the split refuses the pair. An over-approximation, unlike
/// [`source_admits_split`]: every region is admitted from its cut interface,
/// so a source the whole-body admission refuses can be stated in parts.
pub(super) fn pair_may_split(source: &Function, machine: &X86ISelFunction) -> bool {
    let instructions: usize = source
        .blocks
        .values()
        .map(|block| block.instructions.len())
        .sum();
    let rows: usize = machine.blocks.values().map(|block| block.insts.len()).sum();
    source.blocks.len() <= MAX_SPLIT_BLOCKS
        && instructions <= MAX_SPLIT_INSTRUCTIONS
        && machine.blocks.len() <= MAX_SPLIT_BLOCKS
        && rows <= MAX_SPLIT_ROWS
        && machine.name == source.name
        && admitted_frame(source).is_ok_and(|frame| check_entry_parameters(source, &frame).is_ok())
        && source_cfg_bounded(source, MAX_SPLIT_BLOCKS, MAX_SPLIT_INSTRUCTIONS).is_ok()
}

// ---------------------------------------------------------------------------
// Machine rows per LIR instruction (from the TV-1 stamps)
// ---------------------------------------------------------------------------

/// The rows of the machine block that lowers LIR block `lir`, each with the
/// index of the LIR instruction of `lir` its stamp names (`None`: unstamped,
/// or stamped with another block). A jump-table dispatch block the block
/// owns is not included.
pub(super) fn stamped_rows(
    machine: &X86ISelFunction,
    lowered: Block,
    lir: Block,
) -> Vec<Option<usize>> {
    machine.blocks[&lowered]
        .insts
        .iter()
        .map(|inst| {
            inst.lowering_provenance
                .source_id()
                .filter(|id| id.block == lir.0)
                .map(|id| id.index as usize)
        })
        .collect()
}

/// Whether a row transfers control.
fn is_transfer(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::Jcc | X86Opcode::Jmp | X86Opcode::JmpR | X86Opcode::Ret | X86Opcode::Ud2
    )
}

/// A physical register root of an operand (a GPR or an alias of one, or an
/// SSE register).
fn physical_root(operand: &O) -> Option<u16> {
    let O::PReg(preg) = operand else {
        return None;
    };
    match preg.encoding() {
        root @ 0..=15 => Some(root),
        alias @ 16..=31 => Some(alias - GPR32_ALIAS_BASE),
        alias @ 32..=47 => Some(alias - GPR16_ALIAS_BASE),
        alias @ 48..=63 => Some(alias - GPR8_ALIAS_BASE),
        xmm if XMM_ROOTS.contains(&xmm) => Some(xmm),
        _ => None,
    }
}

/// The physical registers a row reads and writes, over-approximated (the
/// planner's choice of a clean split point only; never trusted: a register
/// read across a cut starts [`RegValue::Carried`] or undefined).
fn physical_effects(inst: &X86ISelInst) -> (Vec<u16>, Vec<u16>) {
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    let writes_first = destination_reg(inst).is_some();
    for (index, operand) in inst.operands.iter().enumerate() {
        match operand {
            O::PReg(_) => {
                if let Some(root) = physical_root(operand) {
                    if index == 0 && writes_first {
                        writes.push(root);
                    } else {
                        reads.push(root);
                    }
                }
            }
            O::MemAddr { base, .. } => reads.extend(physical_root(base)),
            O::SibMemAddr { base, index, .. } => {
                reads.extend(physical_root(base));
                reads.extend(physical_root(index));
            }
            _ => {}
        }
    }
    if untied(inst).is_some() {
        reads.extend(inst.operands.first().and_then(physical_root));
    }
    match inst.opcode {
        X86Opcode::Call | X86Opcode::CallR => {
            reads.extend(inst.call_arg_regs.iter().filter_map(|arg| {
                let encoding = arg.reg.encoding();
                physical_root(&O::PReg(arg.reg)).or(Some(encoding))
            }));
            writes.extend(SYSV_CALLER_SAVED_ROOTS);
            writes.extend(XMM_ROOTS);
        }
        X86Opcode::Mul => {
            reads.push(RAX);
            writes.extend([RAX, RDX]);
        }
        X86Opcode::Div | X86Opcode::Idiv => {
            reads.extend([RAX, RDX]);
            writes.extend([RAX, RDX]);
        }
        X86Opcode::Cqo | X86Opcode::Cdq => {
            reads.push(RAX);
            writes.push(RDX);
        }
        X86Opcode::ShlRR | X86Opcode::ShrRR | X86Opcode::SarRR => reads.push(RCX),
        _ => {}
    }
    (reads, writes)
}

/// Whether a row reads the status flags.
fn reads_flags(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::Jcc
            | X86Opcode::Setcc
            | X86Opcode::Cmovcc
            | X86Opcode::Cmovcc32
            | X86Opcode::AdcRR
            | X86Opcode::SbbRR
    )
}

/// Whether a row writes (or clobbers) the status flags.
fn writes_flags(opcode: X86Opcode) -> bool {
    writes_unmodelled_flags(opcode)
        || matches!(
            opcode,
            X86Opcode::CmpRR
                | X86Opcode::CmpRI
                | X86Opcode::TestRR
                | X86Opcode::TestRI
                | X86Opcode::Call
                | X86Opcode::CallR
                | X86Opcode::Div
                | X86Opcode::Idiv
        )
}

/// Whether `inst` opens (`Some(true)`) or closes (`Some(false)`) an outgoing
/// argument area (`sub rsp, n` / `add rsp, n`).
fn outgoing_area(inst: &X86ISelInst) -> Option<bool> {
    match (inst.opcode, inst.operands.as_slice()) {
        (X86Opcode::SubRI, [O::PReg(preg), O::Imm(_)]) if preg.encoding() == RSP => Some(true),
        (X86Opcode::AddRI, [O::PReg(preg), O::Imm(_)]) if preg.encoding() == RSP => Some(false),
        _ => None,
    }
}

/// The split row of a cut before LIR instruction `k` of the block whose
/// machine rows are `rows` (`stamps`: each row's LIR instruction index), when
/// it is a CLEAN stamp boundary: the first row stamped `k` or later, every
/// earlier row stamped before `k` or unstamped, every later one stamped `k`
/// or later or unstamped, at least one stamped row on each side, no transfer
/// before it, and no physical register (but the callee-saved ones and RSP,
/// which hold their entry values), flag or outgoing argument area live there.
pub(super) fn clean_split_row(
    rows: &[X86ISelInst],
    stamps: &[Option<usize>],
    k: usize,
) -> Option<usize> {
    let split = stamps
        .iter()
        .position(|stamp| stamp.is_some_and(|i| i >= k))?;
    if stamps[..split].iter().all(Option::is_none)
        || stamps[..split].iter().flatten().any(|i| *i >= k)
        || stamps[split..].iter().flatten().any(|i| *i < k)
        || rows[..split].iter().any(|inst| is_transfer(inst.opcode))
    {
        return None;
    }
    let open = rows[..split]
        .iter()
        .filter_map(outgoing_area)
        .fold(0i32, |open, opens| if opens { open + 1 } else { open - 1 });
    if open != 0 {
        return None;
    }
    // A `ret` reads the return registers its block writes (the selector's
    // moves into them come right before it).
    let returned: HashSet<u16> = rows
        .iter()
        .flat_map(|inst| physical_effects(inst).1)
        .filter(|root| SYSV_RETURN_ROOTS.contains(root) || SYSV_SSE_RETURN_ROOTS.contains(root))
        .collect();
    let mut written: HashSet<u16> = HashSet::new();
    let mut flags_written = false;
    for inst in &rows[split..] {
        let (mut reads, writes) = physical_effects(inst);
        if inst.opcode == X86Opcode::Ret {
            reads.extend(returned.iter().copied());
        }
        if reads
            .iter()
            .any(|root| !written.contains(root) && !SYSV_PRESERVED_ROOTS.contains(root))
        {
            return None;
        }
        if reads_flags(inst.opcode) && !flags_written {
            return None;
        }
        flags_written |= writes_flags(inst.opcode);
        written.extend(writes);
    }
    Some(split)
}

// ---------------------------------------------------------------------------
// The plan (machine rows per region)
// ---------------------------------------------------------------------------

/// One piece of the planner: instructions `lo..hi` of LIR block `block`, with
/// the machine rows they lower.
#[derive(Debug, Clone)]
struct PlanPiece {
    block: Block,
    lo: usize,
    rows: usize,
    instructions: usize,
    successors: Vec<usize>,
}

/// The values the LIR defines exactly once, each with its one definition's
/// `(block, index)` (an entry parameter is defined by the entry, `None`).
fn single_definitions(source: &Function) -> HashMap<Value, Option<(Block, usize)>> {
    let mut definitions: HashMap<Value, Option<(Block, usize)>> = HashMap::new();
    let mut several: HashSet<Value> = HashSet::new();
    for (value, _) in &source.blocks[&source.entry_block].params {
        definitions.insert(*value, None);
    }
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for block in blocks {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            for result in &inst.results {
                if definitions.insert(*result, Some((*block, index))).is_some() {
                    several.insert(*result);
                }
            }
        }
    }
    for value in several {
        definitions.remove(&value);
    }
    definitions
}

/// A value fixed for the whole run, by its one LIR definition (slice 16):
/// carried exactly across a cut, never generalized.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Leaf {
    /// An `Iconst` (or a copy of one).
    Const,
    /// Parameter `i` of the function (or a copy of it).
    Param(usize),
    /// A `GlobalRef`/`ExternRef` (or a copy of one).
    Symbol(SymbolRef),
}

/// Every value whose one definition is a leaf, through copies.
fn leaves(source: &Function) -> HashMap<Value, Leaf> {
    let definitions = single_definitions(source);
    let mut leaves: HashMap<Value, Leaf> = HashMap::new();
    for (i, (value, _)) in source.blocks[&source.entry_block].params.iter().enumerate() {
        if definitions.get(value) == Some(&None) {
            leaves.insert(*value, Leaf::Param(i));
        }
    }
    // Copies of a leaf, in rounds (a copy may precede its operand's
    // definition in block order).
    loop {
        let mut grown = false;
        let mut values: Vec<(&Value, &Option<(Block, usize)>)> = definitions.iter().collect();
        values.sort_by_key(|(value, _)| value.0);
        for (value, at) in values {
            if leaves.contains_key(value) {
                continue;
            }
            let Some((block, index)) = at else {
                continue;
            };
            let inst = &source.blocks[block].instructions[*index];
            let leaf = match &inst.opcode {
                L::Iconst { ty, .. } if *ty != Type::I128 => Some(Leaf::Const),
                L::GlobalRef { name } | L::ExternRef { name } => Some(Leaf::Symbol(SymbolRef {
                    name: name.clone(),
                    got: matches!(inst.opcode, L::ExternRef { .. }),
                })),
                L::Copy => inst.args.first().and_then(|arg| leaves.get(arg).cloned()),
                _ => None,
            };
            if let Some(leaf) = leaf {
                leaves.insert(*value, leaf);
                grown = true;
            }
        }
        if !grown {
            return leaves;
        }
    }
}

/// The values live at the start of each block (used on some path from it
/// before a redefinition; an edge reads each parameter of its target that it
/// carries unchanged), over the LIR alone.
pub(super) fn live_in(source: &Function, cfg: &SourceCfg) -> HashMap<Block, HashSet<Value>> {
    let mut uses: HashMap<Block, HashSet<Value>> = HashMap::new();
    let mut defs: HashMap<Block, HashSet<Value>> = HashMap::new();
    for block in &cfg.order {
        let (mut used, mut defined) = (HashSet::new(), HashSet::new());
        for inst in &source.blocks[block].instructions {
            for arg in &inst.args {
                if !defined.contains(arg) {
                    used.insert(*arg);
                }
            }
            defined.extend(inst.results.iter().copied());
        }
        // A successor's parameter no copy of this block writes keeps its
        // value along the edge: the edge reads it (a loop header's
        // parameter carried unchanged around the loop).
        for target in &cfg.successors[block] {
            for (param, _) in &source.blocks[target].params {
                if !defined.contains(param) {
                    used.insert(*param);
                }
            }
        }
        uses.insert(*block, used);
        defs.insert(*block, defined);
    }
    let mut live: HashMap<Block, HashSet<Value>> = cfg
        .order
        .iter()
        .map(|block| (*block, HashSet::new()))
        .collect();
    loop {
        let mut changed = false;
        for block in cfg.order.iter().rev() {
            let mut out: HashSet<Value> = HashSet::new();
            for target in &cfg.successors[block] {
                out.extend(live[target].iter().copied());
            }
            let mut new: HashSet<Value> = uses[block].clone();
            new.extend(out.difference(&defs[block]).copied());
            if new != live[block] {
                live.insert(*block, new);
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// A set of private stack bytes of the LIR's slots, one bit per byte.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ByteSet {
    words: Vec<Vec<u64>>,
}

impl ByteSet {
    fn empty(sizes: &[u32]) -> Self {
        Self {
            words: sizes
                .iter()
                .map(|size| vec![0; (*size as usize).div_ceil(64)])
                .collect(),
        }
    }

    /// Whether byte `offset` of slot `slot` is in the set (a byte of a slot
    /// the set does not cover always is: the selector's own slots are never
    /// dead).
    pub(super) fn contains(&self, slot: u32, offset: i64) -> bool {
        let Some(words) = self.words.get(slot as usize) else {
            return true;
        };
        let offset = offset as usize;
        words
            .get(offset / 64)
            .is_none_or(|word| word & (1 << (offset % 64)) != 0)
    }

    fn set(&mut self, slot: u32, range: std::ops::Range<i64>, value: bool) {
        let Some(words) = self.words.get_mut(slot as usize) else {
            return;
        };
        let size = (words.len() * 64) as i64;
        for offset in range.start.max(0)..range.end.min(size) {
            let (word, bit) = ((offset / 64) as usize, offset % 64);
            if value {
                words[word] |= 1 << bit;
            } else {
                words[word] &= !(1 << bit);
            }
        }
    }

    fn set_slot(&mut self, slot: u32) {
        if let Some(words) = self.words.get_mut(slot as usize) {
            words.fill(u64::MAX);
        }
    }

    fn union(&mut self, other: &Self) {
        for (mine, theirs) in self.words.iter_mut().zip(&other.words) {
            for (a, b) in mine.iter_mut().zip(theirs) {
                *a |= b;
            }
        }
    }
}

/// Slice 22 (ruling OD-202): the LIR divisions and remainders of an `I128`,
/// each of which the x86-64 body theorem states as the call of its runtime
/// routine (a call reads every escaping slot, [`live_bytes`]). A value is an
/// `I128` by its own definition: a parameter or block parameter of that type, an `I128`
/// constant, load or extension, a call result the type hints give that type,
/// and every operation whose result has its first operand's type (arithmetic,
/// bitwise, shifts, copies, a select's arms, a division). This only decides
/// liveness, whose errors only refuse: a missed division leaves a byte dead
/// that the call then reads, which refuses by name.
pub(super) fn i128_divisions(source: &Function) -> HashSet<(Block, usize)> {
    let mut wide: HashSet<Value> = HashSet::new();
    // The entry's parameters are `Value(0..)`, one per signature parameter.
    for (i, ty) in source.signature.params.iter().enumerate() {
        if *ty == Type::I128 {
            wide.insert(Value(i as u32));
        }
    }
    for body in source.blocks.values() {
        for (value, ty) in &body.params {
            if *ty == Type::I128 {
                wide.insert(*value);
            }
        }
    }
    for (value, ty) in &source.value_types {
        if *ty == Type::I128 {
            wide.insert(*value);
        }
    }
    let order = source.layout_order();
    for _ in 0..64 {
        let mut grown = false;
        for block in &order {
            let Some(body) = source.blocks.get(block) else {
                continue;
            };
            for inst in &body.instructions {
                let [result] = inst.results.as_slice() else {
                    continue;
                };
                if wide.contains(result) {
                    continue;
                }
                let is_wide = match &inst.opcode {
                    L::Iconst { ty, .. } | L::Load { ty, .. } | L::AtomicLoad { ty, .. } => {
                        *ty == Type::I128
                    }
                    L::Iconst128 { .. } => true,
                    L::Uextend { to_ty, .. } | L::Sextend { to_ty, .. } => *to_ty == Type::I128,
                    L::Copy
                    | L::Iadd
                    | L::Isub
                    | L::Imul
                    | L::Ineg
                    | L::Bnot
                    | L::Band
                    | L::Bor
                    | L::Bxor
                    | L::Ishl
                    | L::Ushr
                    | L::Sshr
                    | L::Udiv
                    | L::Sdiv
                    | L::Urem
                    | L::Srem => inst.args.first().is_some_and(|arg| wide.contains(arg)),
                    L::Select { .. } => inst.args.get(1).is_some_and(|arg| wide.contains(arg)),
                    _ => false,
                };
                if is_wide {
                    wide.insert(*result);
                    grown = true;
                }
            }
        }
        if !grown {
            break;
        }
    }
    let mut divisions = HashSet::new();
    for block in &order {
        let Some(body) = source.blocks.get(block) else {
            continue;
        };
        for (index, inst) in body.instructions.iter().enumerate() {
            if matches!(inst.opcode, L::Udiv | L::Sdiv | L::Urem | L::Srem)
                && inst.args.first().is_some_and(|arg| wide.contains(arg))
            {
                divisions.insert((*block, index));
            }
        }
    }
    divisions
}

/// The private stack bytes LIVE at the start of each block (slice 17, ruling
/// OD-184; the one byte liveness of slice 12's loop headers and slice 16's
/// cut points): read on some path from the block's start before a store
/// overwrites them, over the LIR alone. A byte not live at a cut point is
/// DEAD there: it is left out of the cut's relation on both sides and starts
/// unreadable ([`SlotByte::Dead`]).
///
/// Conservative in every direction a walk could read more: a private address
/// is tracked only through a value's one definition (`StackAddr`, then
/// `Copy`, `Bitcast`, `StructGep` and `Iadd` of an `Iconst`, or of anything
/// else as an address at an unknown offset); a load through one at a known
/// offset reads its bytes, at an unknown offset (an indexed access, whose
/// select reads every candidate, and whose store update reads the byte before
/// it) every byte of its slot; only a store at a known offset overwrites. A
/// slot whose address is used in any other way (passed to a call or a C
/// memory routine, stored as data, returned, compared, joined) ESCAPES, and
/// every call, and every load or store through an address the analysis does
/// not track (which may derive from an escaped slot, slice 15), reads every
/// byte of every escaping slot; any instruction that uses a slot's address
/// other than as an access's address reads every byte of that slot. A slot
/// the LIR does not declare (the selector's aggregate copies and call-result
/// slots) is never dead. A liveness error only refuses: a byte called dead
/// that a walk reads is an unreadable byte (no claim).
pub(super) fn live_bytes(source: &Function, cfg: &SourceCfg) -> HashMap<Block, ByteSet> {
    let wide_divisions = i128_divisions(source);
    let sizes: Vec<u32> = source.stack_slots.iter().map(|slot| slot.size).collect();
    let definitions = single_definitions(source);
    let constant = |value: &Value| -> Option<i64> {
        let mut value = *value;
        for _ in 0..64 {
            let (block, index) = (*definitions.get(&value)?)?;
            let inst = &source.blocks[&block].instructions[index];
            match &inst.opcode {
                L::Iconst { ty, imm } if *ty != Type::I128 => return Some(*imm),
                L::Copy | L::Bitcast { .. } => value = inst.args[0],
                _ => return None,
            }
        }
        None
    };
    // Every tracked private address: its slot and its constant offset, if
    // known; and the values each address-deriving instruction reads.
    let mut addresses: HashMap<Value, (u32, Option<i64>)> = HashMap::new();
    let mut derived_from: HashSet<(Block, usize)> = HashSet::new();
    for _ in 0..64 {
        let mut grown = false;
        for block in &cfg.order {
            for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
                let [result] = inst.results.as_slice() else {
                    continue;
                };
                if addresses.contains_key(result) || !definitions.contains_key(result) {
                    continue;
                }
                let tracked = match &inst.opcode {
                    L::StackAddr { slot } if (*slot as usize) < sizes.len() => {
                        Some((*slot, Some(0)))
                    }
                    L::Copy | L::Bitcast { .. } => addresses.get(&inst.args[0]).copied(),
                    L::StructGep {
                        struct_ty,
                        field_index,
                    } => addresses.get(&inst.args[0]).map(|(slot, offset)| {
                        let field = field_offset(struct_ty, *field_index);
                        (
                            *slot,
                            offset.zip(field).and_then(|(offset, field)| {
                                offset.checked_add(i64::try_from(field).ok()?)
                            }),
                        )
                    }),
                    L::Iadd => {
                        let (a, b) = (inst.args[0], inst.args[1]);
                        match (addresses.get(&a), addresses.get(&b)) {
                            (Some((slot, offset)), None) | (None, Some((slot, offset))) => {
                                let other = if addresses.contains_key(&a) { b } else { a };
                                Some((
                                    *slot,
                                    offset
                                        .zip(constant(&other))
                                        .and_then(|(offset, k)| offset.checked_add(k)),
                                ))
                            }
                            _ => None,
                        }
                    }
                    // OD-185: an array element of a tracked address (its
                    // base operand only), at a known offset when the index
                    // is a constant.
                    L::ArrayGep { elem_ty } => {
                        match (addresses.get(&inst.args[0]), addresses.get(&inst.args[1])) {
                            (Some((slot, offset)), None) => {
                                let element = constant(&inst.args[1])
                                    .zip(
                                        array_element_stride(elem_ty)
                                            .and_then(|stride| i64::try_from(stride).ok()),
                                    )
                                    .and_then(|(k, stride)| k.checked_mul(stride));
                                Some((
                                    *slot,
                                    offset
                                        .zip(element)
                                        .and_then(|(offset, element)| offset.checked_add(element)),
                                ))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                if let Some(tracked) = tracked {
                    addresses.insert(*result, tracked);
                    derived_from.insert((*block, index));
                    grown = true;
                }
            }
        }
        if !grown {
            break;
        }
    }
    // The role each use of a tracked address plays: an access's address, the
    // operand of an address it derives, or anything else (the slot escapes).
    let address_operand = |inst: &Instruction, k: usize| match inst.opcode {
        L::Load { .. } | L::AtomicLoad { .. } => k == 0,
        L::Store { .. } | L::AtomicStore { .. } => k == 1,
        _ => false,
    };
    let mut escaping: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for block in &cfg.order {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            for (k, arg) in inst.args.iter().enumerate() {
                if let Some((slot, _)) = addresses.get(arg)
                    && !address_operand(inst, k)
                    && !derived_from.contains(&(*block, index))
                {
                    escaping.insert(*slot);
                }
            }
        }
    }
    let width = |ty: &Type| Carrier::of(ty).map_or(16, |carrier| i64::from(carrier.bytes()));
    // One instruction's effect, backward: what it overwrites, then what it
    // reads.
    let step = |live: &mut ByteSet, block: Block, index: usize, inst: &Instruction| {
        let read_escaping = |live: &mut ByteSet| {
            for slot in &escaping {
                live.set_slot(*slot);
            }
        };
        match &inst.opcode {
            L::Load { ty, .. } | L::AtomicLoad { ty, .. } => match addresses.get(&inst.args[0]) {
                Some((slot, Some(offset))) => live.set(*slot, *offset..*offset + width(ty), true),
                Some((slot, None)) => live.set_slot(*slot),
                None => read_escaping(live),
            },
            L::Store { ty, .. } | L::AtomicStore { ty, .. } => match addresses.get(&inst.args[1]) {
                Some((slot, Some(offset))) => {
                    live.set(*slot, *offset..*offset + width(ty), false);
                }
                Some((slot, None)) => live.set_slot(*slot),
                None => read_escaping(live),
            },
            L::Call { .. } | L::CallIndirect | L::Memcpy | L::Memmove | L::Memset => {
                read_escaping(live)
            }
            // Slice 22 (ruling OD-202): an `I128` division is the call of its
            // runtime routine, which the theorem states as any call.
            L::Udiv | L::Sdiv | L::Urem | L::Srem if wide_divisions.contains(&(block, index)) => {
                read_escaping(live)
            }
            _ => {}
        }
        for (k, arg) in inst.args.iter().enumerate() {
            if let Some((slot, _)) = addresses.get(arg)
                && !address_operand(inst, k)
                && !derived_from.contains(&(block, index))
            {
                live.set_slot(*slot);
            }
        }
    };
    let mut live: HashMap<Block, ByteSet> = cfg
        .order
        .iter()
        .map(|block| (*block, ByteSet::empty(&sizes)))
        .collect();
    loop {
        let mut changed = false;
        for block in cfg.order.iter().rev() {
            let mut current = ByteSet::empty(&sizes);
            for target in &cfg.successors[block] {
                if let Some(known) = live.get(target) {
                    current.union(known);
                }
            }
            for (index, inst) in source.blocks[block].instructions.iter().enumerate().rev() {
                step(&mut current, *block, index, inst);
            }
            if live[block] != current {
                live.insert(*block, current);
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// The bytes of the LIR's slots DEAD at the start of `block` ([`live_bytes`]).
pub(super) fn dead_bytes(
    source: &Function,
    live: &HashMap<Block, ByteSet>,
    block: Block,
) -> std::collections::BTreeSet<(u32, i64)> {
    let Some(live) = live.get(&block) else {
        return std::collections::BTreeSet::new();
    };
    source
        .stack_slots
        .iter()
        .enumerate()
        .flat_map(|(slot, info)| (0..i64::from(info.size)).map(move |offset| (slot as u32, offset)))
        .filter(|(slot, offset)| !live.contains(*slot, *offset))
        .collect()
}

/// The trailing run of `Copy` instructions before a block's terminator (the
/// adapter's edge copies): a cut inside it, or between it and the
/// terminator, would separate a block parameter's copies from their edge.
pub(super) fn trailing_copies(block: &trust_cg_lower::function::BasicBlock) -> usize {
    let Some((_, body)) = block.instructions.split_last() else {
        return 0;
    };
    body.iter()
        .rev()
        .take_while(|inst| matches!(inst.opcode, L::Copy))
        .count()
}

/// The program points (`(block, index)`, the index 0 a block start) a
/// function past the single-query bounds is cut at, besides its entry and
/// its loop headers (slice 16): first every block of more than a quarter of
/// the region budget is cut into PIECES at clean stamp boundaries
/// ([`clean_split_row`]) near even splits, each the boundary with the fewest
/// live values that are not fixed for the run; then, while a region (slice
/// 12's, over the pieces) is over budget, the over-budget region with the
/// most rows gets one more cut at the piece that keeps its head the largest
/// that fits (ties by the least total rows over all regions, then by piece
/// order); failing that, the cut that makes the largest region smallest.
/// No point in `banned` is chosen. Deterministic; it only CHOOSES the cuts
/// (any choice that keeps the loop headers is sound).
pub(super) fn plan_points(
    source: &Function,
    cfg: &SourceCfg,
    machine: &X86ISelFunction,
    correspondence: &Correspondence,
    policy: &SplitPolicy,
    banned: &std::collections::BTreeSet<(Block, usize)>,
) -> Result<Vec<(Block, usize)>, X86BodyRefusal> {
    let no_plan = |detail: String| {
        unsupported(X86BodyUnsupported::SourceShape(format!(
            "no cut plan fits the region bounds ({} rows, {} instructions, {} blocks per region, \
             {} parts): {detail}",
            policy.region_rows, policy.region_instructions, policy.region_blocks, policy.max_parts
        )))
    };
    let leaves = leaves(source);
    let live = live_in(source, cfg);
    let headers: HashSet<Block> = cfg.loops.iter().map(|lp| lp.header).collect();
    // The values a `StackAddr` defines (private addresses, carried exactly).
    let addresses: HashSet<Value> = single_definitions(source)
        .into_iter()
        .filter_map(|(value, at)| {
            let (block, index) = at?;
            matches!(
                source.blocks[&block].instructions[index].opcode,
                L::StackAddr { .. }
            )
            .then_some(value)
        })
        .collect();
    // Charge each dispatch block's rows to the block whose `Switch` it
    // dispatches.
    let mut extra: HashMap<Block, usize> = HashMap::new();
    for (dispatch, owner) in &correspondence.dispatch {
        if let Some(lir) = correspondence.origin.get(owner) {
            *extra.entry(*lir).or_default() += machine.blocks[dispatch].insts.len();
        }
    }
    let piece_rows = (policy.region_rows / 4).max(16);
    let mut pieces: Vec<PlanPiece> = Vec::new();
    let mut first_piece: HashMap<Block, usize> = HashMap::new();
    let mut last_piece: HashMap<Block, usize> = HashMap::new();
    for block in &cfg.order {
        let body = &source.blocks[block];
        let n = body.instructions.len();
        // Slice 24c (OD-228): a segment member other than its head lowers no
        // machine block of its own (its rows are its segment's, charged to
        // the head): one piece of no rows, never cut ([`segment::bans`]).
        if correspondence.segments.inner(*block).is_some() {
            first_piece.insert(*block, pieces.len());
            last_piece.insert(*block, pieces.len());
            pieces.push(PlanPiece {
                block: *block,
                lo: 0,
                rows: 0,
                instructions: n,
                successors: Vec::new(),
            });
            continue;
        }
        let lowered = correspondence.lowering[block];
        let rows = &machine.blocks[&lowered].insts;
        let stamps = stamped_rows(machine, lowered, *block);
        let total = rows.len() + extra.get(block).copied().unwrap_or(0);
        // Boundaries: each `(k, split row)`, ascending.
        let mut bounds: Vec<(usize, usize)> = vec![(0, 0)];
        let last_cut = n.saturating_sub(1 + trailing_copies(body));
        // Slice 24c: a segment's head is never cut inside: one piece, all
        // of its machine block's rows.
        let head = correspondence.segments.of_head(*block).is_some();
        if rows.len() > piece_rows && last_cut >= 1 && !head {
            // Live values that are no leaf and no private address, at each
            // instruction boundary (backward from the block's end).
            let fixed = |value: &Value| leaves.contains_key(value) || addresses.contains(value);
            let mut current: HashSet<Value> = HashSet::new();
            for target in &cfg.successors[block] {
                current.extend(live[target].iter().copied());
            }
            let mut weight = vec![0usize; n + 1];
            weight[n] = current.iter().filter(|value| !fixed(value)).count();
            for i in (0..n).rev() {
                let inst = &body.instructions[i];
                for result in &inst.results {
                    current.remove(result);
                }
                current.extend(inst.args.iter().copied());
                weight[i] = current.iter().filter(|value| !fixed(value)).count();
            }
            let step = (piece_rows * n / rows.len().max(1)).max(1);
            let mut position = step;
            while position <= last_cut {
                let previous = bounds.last().expect("the start").0;
                let window = (step / 4).max(1);
                let low = (previous + 1).max(position.saturating_sub(window));
                let high = last_cut.min(position + window);
                let best = (low..=high)
                    .filter_map(|k| clean_split_row(rows, &stamps, k).map(|row| (k, row)))
                    .min_by_key(|(k, _)| (weight[*k], k.abs_diff(position), *k));
                let Some((k, row)) = best.or_else(|| {
                    ((previous + 1)..=last_cut)
                        .filter_map(|k| clean_split_row(rows, &stamps, k).map(|row| (k, row)))
                        .min_by_key(|(k, _)| (k.abs_diff(position), weight[*k], *k))
                }) else {
                    break;
                };
                if row <= bounds.last().expect("the start").1 {
                    break;
                }
                bounds.push((k, row));
                position = k + step;
            }
        }
        let first = pieces.len();
        for (j, &(lo, row)) in bounds.iter().enumerate() {
            let (hi, end) = match bounds.get(j + 1) {
                Some(&(hi, end)) => (hi, end),
                None => (n, total),
            };
            pieces.push(PlanPiece {
                block: *block,
                lo,
                rows: end - row,
                instructions: hi - lo,
                successors: Vec::new(),
            });
        }
        first_piece.insert(*block, first);
        last_piece.insert(*block, pieces.len() - 1);
        for j in first..pieces.len() - 1 {
            pieces[j].successors = vec![j + 1];
        }
    }
    for block in &cfg.order {
        let last = last_piece[block];
        pieces[last].successors = cfg.successors[block]
            .iter()
            .map(|target| first_piece[target])
            .collect();
    }
    if let Some(piece) = pieces.iter().find(|piece| piece.rows > policy.region_rows) {
        return Err(no_plan(format!(
            "instructions {}.. of block {:?} lower to {} rows with no clean cut inside",
            piece.lo, piece.block, piece.rows
        )));
    }
    let regions = |cuts: &std::collections::BTreeSet<usize>| -> Vec<(usize, Vec<usize>)> {
        cuts.iter()
            .map(|&start| {
                let mut members: std::collections::BTreeSet<usize> =
                    std::collections::BTreeSet::from([start]);
                let mut work = vec![start];
                while let Some(piece) = work.pop() {
                    for &target in &pieces[piece].successors {
                        if !cuts.contains(&target) && members.insert(target) {
                            work.push(target);
                        }
                    }
                }
                (start, members.into_iter().collect())
            })
            .collect()
    };
    let size = |members: &[usize]| -> (usize, usize, usize) {
        (
            members.iter().map(|piece| pieces[*piece].rows).sum(),
            members
                .iter()
                .map(|piece| pieces[*piece].instructions)
                .sum(),
            members.len(),
        )
    };
    let over = |(rows, instructions, blocks): (usize, usize, usize)| {
        rows > policy.region_rows
            || instructions > policy.region_instructions
            || blocks > policy.region_blocks
    };
    let mut cuts: std::collections::BTreeSet<usize> =
        std::collections::BTreeSet::from([first_piece[&source.entry_block]]);
    for header in &headers {
        cuts.insert(first_piece[header]);
    }
    for _ in 0..pieces.len() {
        let current = regions(&cuts);
        let Some((worst, members)) = current
            .iter()
            .filter(|(_, members)| over(size(members)))
            .max_by_key(|(start, members)| (size(members), std::cmp::Reverse(*start)))
        else {
            break;
        };
        let mut best: Option<((usize, usize, usize, usize), usize)> = None;
        for &candidate in members {
            if cuts.contains(&candidate)
                || banned.contains(&(pieces[candidate].block, pieces[candidate].lo))
            {
                continue;
            }
            let mut trial = cuts.clone();
            trial.insert(candidate);
            let split = regions(&trial);
            let head = split
                .iter()
                .find(|(start, _)| start == worst)
                .map(|(_, members)| size(members))
                .expect("the worst region");
            let total: usize = split.iter().map(|(_, members)| size(members).0).sum();
            let key = if !over(head) {
                (0, usize::MAX - head.0, total, candidate)
            } else {
                let largest = split
                    .iter()
                    .map(|(_, members)| {
                        let (rows, instructions, _) = size(members);
                        (rows * 1024 / policy.region_rows.max(1))
                            .max(instructions * 1024 / policy.region_instructions.max(1))
                    })
                    .max()
                    .unwrap_or(0);
                (1, largest, total, candidate)
            };
            if best.as_ref().is_none_or(|(known, _)| key < *known) {
                best = Some((key, candidate));
            }
        }
        let Some((_, chosen)) = best else {
            break;
        };
        cuts.insert(chosen);
    }
    let final_regions = regions(&cuts);
    if let Some((start, members)) = final_regions
        .iter()
        .find(|(_, members)| over(size(members)))
    {
        let (rows, instructions, blocks) = size(members);
        return Err(no_plan(format!(
            "the region from instructions {}.. of block {:?} keeps {rows} rows, {instructions} \
             instructions and {blocks} blocks",
            pieces[*start].lo, pieces[*start].block
        )));
    }
    if final_regions.len() > policy.max_parts {
        return Err(no_plan(format!("{} regions", final_regions.len())));
    }
    let mut points: Vec<(Block, usize)> = cuts
        .iter()
        .map(|piece| (pieces[*piece].block, pieces[*piece].lo))
        .filter(|(block, lo)| {
            !(*block == source.entry_block && *lo == 0) && !(*lo == 0 && headers.contains(block))
        })
        .collect();
    points.sort();
    Ok(points)
}

// ---------------------------------------------------------------------------
// Pieces: the cut blocks, rewritten
// ---------------------------------------------------------------------------

/// A source and its machine stream with every mid-block cut point made a
/// block start ([`rewrite_pieces`]).
pub(super) struct Pieces {
    pub(super) source: Function,
    pub(super) machine: X86ISelFunction,
    /// Each block of `source` that a cut created -> the original block and the
    /// index there of its first instruction.
    pub(super) origin: HashMap<Block, (Block, usize)>,
    /// The block each planned point starts.
    pub(super) cuts: Vec<Block>,
}

impl Pieces {
    /// A LIR location of the rewritten source as the original's.
    pub(super) fn original(&self, block: Block, index: usize) -> (Block, usize) {
        match self.origin.get(&block) {
            Some((original, first)) if index != JOIN_ROW => (*original, first + index),
            Some((original, _)) => (*original, index),
            None => (block, index),
        }
    }
}

/// Cut block `B` before instruction `k` for every point `(B, k)`, `k > 0`, of
/// `points`: on the LIR, `B` keeps instructions `0..k` and ends in a `Jump` to
/// a new block holding the rest (a new block's parameters are none); on the
/// machine, the block lowering `B` keeps the rows before the point's clean
/// split row ([`clean_split_row`]) and falls through to a new block, laid out
/// right after it, holding the rest, its stamps renumbered to the new LIR
/// block. Every row keeps its walk ordinal (checked). A point that is no
/// clean stamp boundary makes no claim. A new block's id is at least `floor`
/// (checked): slice 24a's quotient passes one above every block id of the
/// ORIGINAL pair, so no piece takes the id of a block it absorbed
/// ([`quotient::Quotient::floor`]); for an uncontracted pair it is one above
/// the pair's own ids, the first id this function would choose anyway.
pub(super) fn rewrite_pieces(
    source: &Function,
    machine: &X86ISelFunction,
    correspondence: &Correspondence,
    points: &[(Block, usize)],
    floor: u32,
) -> Result<Pieces, X86BodyRefusal> {
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    let mut source_out = source.clone();
    let mut machine_out = machine.clone();
    let mut origin: HashMap<Block, (Block, usize)> = HashMap::new();
    let mut cuts: Vec<Block> = Vec::new();
    let own = source
        .blocks
        .keys()
        .chain(machine.blocks.keys())
        .map(|block| block.0)
        .max()
        .unwrap_or(0)
        + 1;
    let mut next = if mutated("floor-off") {
        own
    } else {
        own.max(floor)
    };
    let mut by_block: std::collections::BTreeMap<Block, Vec<usize>> =
        std::collections::BTreeMap::new();
    for &(block, k) in points {
        if !source.blocks.contains_key(&block) {
            return Err(no_claim(format!(
                "a cut point in block {block:?}, which has no body"
            )));
        }
        if k == 0 {
            cuts.push(block);
        } else {
            by_block.entry(block).or_default().push(k);
        }
    }
    for (block, mut ks) in by_block {
        ks.sort_unstable();
        ks.dedup();
        let body = &source.blocks[&block];
        let n = body.instructions.len();
        let last_cut = n.saturating_sub(1 + trailing_copies(body));
        if ks.iter().any(|k| *k > last_cut) {
            return Err(no_claim(format!(
                "a cut inside the edge copies or terminator of block {block:?}"
            )));
        }
        let lowered = correspondence.lowering[&block];
        let rows = machine.blocks[&lowered].insts.clone();
        let stamps = stamped_rows(machine, lowered, block);
        let mut splits = Vec::with_capacity(ks.len());
        for &k in &ks {
            let row = clean_split_row(&rows, &stamps, k).ok_or_else(|| {
                no_claim(format!(
                    "the machine rows of block {block:?} do not split cleanly before its \
                     instruction {k}"
                ))
            })?;
            if splits.last().is_some_and(|previous| row <= *previous) {
                return Err(no_claim(format!(
                    "two cuts in block {block:?} split its machine rows at one row"
                )));
            }
            splits.push(row);
        }
        let new_blocks: Vec<Block> = ks
            .iter()
            .map(|_| {
                next += 1;
                Block(next - 1)
            })
            .collect();
        // LIR: the pieces, each but the last ending in a `Jump` to the next.
        let instructions = body.instructions.clone();
        let locs = body.source_locs.clone();
        let origins = source.trust_ir_origins.get(&block).cloned();
        let bounds: Vec<usize> = std::iter::once(0)
            .chain(ks.iter().copied())
            .chain(std::iter::once(n))
            .collect();
        let piece_blocks: Vec<Block> = std::iter::once(block)
            .chain(new_blocks.iter().copied())
            .collect();
        for (j, piece) in piece_blocks.iter().enumerate() {
            let (lo, hi) = (bounds[j], bounds[j + 1]);
            let mut piece_instructions: Vec<Instruction> = instructions[lo..hi].to_vec();
            let mut piece_locs: Vec<_> = (lo..hi).map(|i| locs.get(i).cloned().flatten()).collect();
            let mut piece_origins: Option<Vec<_>> = origins.as_ref().map(|origins| {
                (lo..hi)
                    .map(|i| origins.get(i).cloned().flatten())
                    .collect()
            });
            if let Some(following) = piece_blocks.get(j + 1) {
                piece_instructions.push(Instruction {
                    opcode: L::Jump { dest: *following },
                    args: Vec::new(),
                    results: Vec::new(),
                });
                piece_locs.push(None);
                if let Some(origins) = piece_origins.as_mut() {
                    origins.push(None);
                }
            }
            let params = if j == 0 {
                body.params.clone()
            } else {
                Vec::new()
            };
            source_out.blocks.insert(
                *piece,
                trust_cg_lower::function::BasicBlock {
                    params,
                    instructions: piece_instructions,
                    source_locs: if locs.is_empty() {
                        Vec::new()
                    } else {
                        piece_locs
                    },
                },
            );
            if let Some(origins) = piece_origins {
                source_out.trust_ir_origins.insert(*piece, origins);
            }
            if j > 0 {
                origin.insert(*piece, (block, lo));
            }
        }
        if !source_out.block_order.is_empty() {
            let at = source_out
                .block_order
                .iter()
                .position(|known| *known == block)
                .expect("an ordered block");
            for (offset, piece) in new_blocks.iter().enumerate() {
                source_out.block_order.insert(at + 1 + offset, *piece);
            }
        }
        cuts.extend(new_blocks.iter().copied());
        // Machine: the rows before each split row, then the next piece's,
        // each piece falling through to the next.
        let successors = machine.blocks[&lowered].successors.clone();
        let row_bounds: Vec<usize> = std::iter::once(0)
            .chain(splits.iter().copied())
            .chain(std::iter::once(rows.len()))
            .collect();
        let machine_blocks: Vec<Block> = std::iter::once(lowered)
            .chain(new_blocks.iter().copied())
            .collect();
        for (j, piece) in machine_blocks.iter().enumerate() {
            let mut insts: Vec<X86ISelInst> = rows[row_bounds[j]..row_bounds[j + 1]].to_vec();
            if j > 0 {
                let renumbered = piece_blocks[j];
                let first = bounds[j];
                for inst in &mut insts {
                    if let trust_cg_ir::provenance::LoweringProvenance::SourceInst { id, .. } =
                        &mut inst.lowering_provenance
                        && id.block == block.0
                    {
                        id.block = renumbered.0;
                        id.index -= first as u32;
                    }
                }
            }
            let piece_successors = match machine_blocks.get(j + 1) {
                Some(following) => vec![*following],
                None => successors.clone(),
            };
            machine_out.blocks.insert(
                *piece,
                trust_cg_lower::x86_64_isel::X86ISelBlock {
                    insts,
                    successors: piece_successors,
                },
            );
        }
        let at = machine_out
            .block_order
            .iter()
            .position(|known| *known == lowered)
            .expect("a laid-out machine block");
        for (offset, piece) in new_blocks.iter().enumerate() {
            machine_out.block_order.insert(at + 1 + offset, *piece);
        }
        // A row of another machine block stamped with this block's
        // instructions (a jump-table dispatch block, the tail of its
        // `Switch`) is renumbered to the piece that holds the instruction.
        for (other, body) in machine_out.blocks.iter_mut() {
            if machine_blocks.contains(other) {
                continue;
            }
            for inst in &mut body.insts {
                if let trust_cg_ir::provenance::LoweringProvenance::SourceInst { id, .. } =
                    &mut inst.lowering_provenance
                    && id.block == block.0
                    && let Some(j) = (1..piece_blocks.len())
                        .rev()
                        .find(|j| id.index as usize >= bounds[*j])
                {
                    id.block = piece_blocks[j].0;
                    id.index -= bounds[j] as u32;
                }
            }
        }
    }
    // The rewritten stream is the original's rows, in the original order.
    let flatten = |function: &X86ISelFunction| -> Vec<(X86Opcode, Vec<O>)> {
        function
            .block_order
            .iter()
            .flat_map(|block| function.blocks[block].insts.iter())
            .map(|inst| (inst.opcode, inst.operands.clone()))
            .collect()
    };
    if flatten(&machine_out) != flatten(machine) {
        return Err(unsupported(X86BodyUnsupported::Construction(
            "the cut machine stream is not the original's rows in order".into(),
        )));
    }
    let mut pieces: Vec<&Block> = origin.keys().collect();
    pieces.sort_unstable();
    if let Some(piece) = pieces.into_iter().find(|piece| piece.0 < floor) {
        return Err(unsupported(X86BodyUnsupported::Construction(format!(
            "cut piece {piece:?} takes an id below the floor {floor} of the original pair's \
             block ids"
        ))));
    }
    cuts.sort_unstable();
    cuts.dedup();
    Ok(Pieces {
        source: source_out,
        machine: machine_out,
        origin,
        cuts,
    })
}

// ---------------------------------------------------------------------------
// The cut interface: the source side
// ---------------------------------------------------------------------------

/// A value fixed for the run at a cut point, carried exactly (slice 16).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Closed {
    /// An `Iconst`'s bits at its carrier.
    Const { carrier: Carrier, bits: u64 },
    /// Parameter `index` of the function.
    Param { carrier: Carrier, index: usize },
    /// A symbol's address.
    Symbol(SymbolRef),
    /// A private stack address (with the aggregate type a by-value aggregate
    /// value has); no SMT term.
    Frame {
        address: FrameAddr,
        aggregate: Option<Type>,
    },
}

/// One private byte of a cut interface (slice 16).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ByteEntry {
    /// A free input `x{C}b{slot}o{offset}` both sides share at the cut, with
    /// whether every edge's byte is one a `bool` read may read and whether
    /// some edge's may be tainted (as [`SlotByte::Header`]).
    Input { bool_read: bool, tainted: bool },
    /// The same byte fixed for the run on every edge (a stored constant or
    /// parameter, an aggregate parameter's register byte, a stored private
    /// address), carried exactly.
    Closed(SlotByte),
}

/// The interface of one cut point (slice 16): its items and closed values,
/// its bytes, and the slots that escaped on some edge into it.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct CutInterface {
    pub(super) block: Block,
    pub(super) region: usize,
    /// The value items, in order: the cut block's parameters, then every other
    /// live value that is not closed, ascending.
    pub(super) items: Vec<(Value, Carrier)>,
    /// How many leading items are the cut block's parameters.
    pub(super) params: usize,
    /// The closed values, by value id.
    pub(super) closed: std::collections::BTreeMap<u32, (Value, Closed)>,
    /// Every byte some edge into the cut wrote, by `(slot, offset)`.
    pub(super) bytes: std::collections::BTreeMap<(u32, i64), ByteEntry>,
    /// The items some edge gives a value that may derive from an escaped
    /// slot (slice 7's retention rule).
    pub(super) tainted: std::collections::BTreeSet<u32>,
    /// The slots that escaped on some edge into the cut.
    pub(super) escaped: std::collections::BTreeSet<u32>,
    /// Slice 17 (OD-184): the bytes DEAD at the cut ([`live_bytes`]): left
    /// out of its relation and assumptions on both sides, unreadable in its
    /// region.
    pub(super) dead: std::collections::BTreeSet<(u32, i64)>,
}

impl CutInterface {
    /// The source state at the start of the cut's region: each item a value
    /// of its carrier (its term the input `x{C}v{i}`), each closed value as
    /// it is on every edge, each byte item [`SlotByte::Header`] of the cut
    /// (its term `x{C}b{slot}o{offset}`), each closed byte as it is; every
    /// other value undefined and every other byte unwritten.
    pub(super) fn start(&self, frame_facts: &SourceFrame) -> AdmitState {
        let mut state = AdmitState {
            types: HashMap::new(),
            affine: HashMap::new(),
            constants: HashMap::new(),
            frame: HashMap::new(),
            indexed: HashMap::new(),
            slot_bytes: frame_facts
                .slot_sizes
                .iter()
                .map(|size| vec![None; *size as usize])
                .collect(),
            aggregates: HashMap::new(),
            tainted_sites: HashSet::new(),
            escaped: std::collections::BTreeSet::new(),
            tainted: HashSet::new(),
        };
        for (value, carrier) in &self.items {
            state.types.insert(*value, *carrier);
            if self.tainted.contains(&value.0) {
                state.tainted.insert(*value);
            }
        }
        for (value, closed) in self.closed.values() {
            match closed {
                Closed::Const { carrier, bits } => {
                    state.types.insert(*value, *carrier);
                    state.constants.insert(*value, *bits);
                    if *carrier == Carrier::I64 {
                        state
                            .affine
                            .insert(*value, Affine::constant(*bits, u64::MAX));
                    }
                }
                Closed::Param { carrier, index } => {
                    state.types.insert(*value, *carrier);
                    if *carrier == Carrier::I64
                        && let Some(affine) = parameter_affine(*index)
                    {
                        state.affine.insert(*value, affine);
                    }
                }
                Closed::Symbol(_) => {
                    state.types.insert(*value, Carrier::I64);
                }
                Closed::Frame { address, aggregate } => {
                    state.types.insert(*value, Carrier::I64);
                    state.frame.insert(*value, *address);
                    if let Some(ty) = aggregate {
                        state.aggregates.insert(*value, ty.clone());
                    }
                }
            }
        }
        for (&(slot, offset), entry) in &self.bytes {
            state.slot_bytes[slot as usize][offset as usize] = Some(match entry {
                ByteEntry::Input { bool_read, tainted } => SlotByte::Header {
                    header: self.block,
                    bool_read: *bool_read,
                    tainted: *tainted,
                },
                ByteEntry::Closed(byte) => *byte,
            });
        }
        // Slice 17: a dead byte starts unreadable.
        for &(slot, offset) in &self.dead {
            state.slot_bytes[slot as usize][offset as usize] = Some(SlotByte::Dead);
        }
        let mut escaped = std::collections::BTreeSet::new();
        escape_source(
            &mut escaped,
            &state.slot_bytes,
            self.escaped.iter().copied().collect::<Vec<_>>(),
        );
        state.escaped = escaped;
        state
    }
}

/// The closed value `value` is on one edge, given its state, or `None` when
/// it is not closed there.
fn closed_on(value: Value, state: &AdmitState, leaves: &HashMap<Value, Leaf>) -> Option<Closed> {
    if let Some(address) = state.frame.get(&value) {
        return Some(Closed::Frame {
            address: *address,
            aggregate: state.aggregates.get(&value).cloned(),
        });
    }
    let carrier = *state.types.get(&value)?;
    match leaves.get(&value)? {
        Leaf::Const => Some(Closed::Const {
            carrier,
            bits: *state.constants.get(&value)?,
        }),
        Leaf::Param(index) => Some(Closed::Param {
            carrier,
            index: *index,
        }),
        Leaf::Symbol(symbol) => Some(Closed::Symbol(symbol.clone())),
    }
}

/// The interface of cut point `cut` (region `region`) from the cut edges
/// into it (`edges`, by their source block), joined with what an earlier
/// round assumed (`previous`): every round only grows an assumption (a byte
/// item, a tainted item, an escaped slot). A live value some edge does not
/// define at one carrier, a parameter an edge gives a private address, an
/// `I128` item, or a byte some edge leaves holding a stored private address
/// that another edge does not is outside the domain.
#[allow(clippy::too_many_arguments)]
fn interface_of(
    source: &Function,
    cut: Block,
    region: usize,
    edges: &[&CutEdge],
    previous: Option<&CutInterface>,
    live: &HashSet<Value>,
    dead: &std::collections::BTreeSet<(u32, i64)>,
    leaves: &HashMap<Value, Leaf>,
    sites: &mut SourceSites,
) -> Result<CutInterface, X86BodyRefusal> {
    let domain = |reason: String| unsupported(X86BodyUnsupported::SourceDomain(reason));
    let params = &source.blocks[&cut].params;
    let mut items: Vec<(Value, Carrier)> = Vec::new();
    let mut tainted: std::collections::BTreeSet<u32> = previous
        .map(|previous| previous.tainted.clone())
        .unwrap_or_default();
    for (k, (param, ty)) in params.iter().enumerate() {
        // Slice 20 (ruling OD-193): an `I128` item is two 64-bit halves.
        let carrier = match Carrier::of(ty) {
            None => {
                return Err(domain(format!(
                    "cut point {cut:?} parameter {param:?} has type {ty:?} (a non-scalar value \
                     crossing a cut, outside the lane)"
                )));
            }
            Some(carrier) => carrier,
        };
        for edge in edges {
            let value = edge.values[k];
            if edge.state.frame.contains_key(&value)
                || edge.state.indexed.contains_key(&value)
                || edge.state.aggregates.contains_key(&value)
            {
                return Err(domain(format!(
                    "cut point {cut:?} parameter {param:?} is a private stack address on an edge \
                     into it (outside the lane)"
                )));
            }
            if edge.state.types.get(&value) != Some(&carrier) {
                return Err(domain(format!(
                    "cut point {cut:?} parameter {param:?} is not defined at its type on every \
                     edge into it"
                )));
            }
            if edge.state.tainted.contains(&value) {
                tainted.insert(param.0);
            }
        }
        items.push((*param, carrier));
    }
    let param_values: HashSet<Value> = params.iter().map(|(value, _)| *value).collect();
    let mut live_values: Vec<Value> = live
        .iter()
        .filter(|value| !param_values.contains(value))
        .copied()
        .collect();
    live_values.sort_unstable_by_key(|value| value.0);
    let mut closed: std::collections::BTreeMap<u32, (Value, Closed)> =
        std::collections::BTreeMap::new();
    for value in live_values {
        let carriers: Vec<Option<&Carrier>> = edges
            .iter()
            .map(|edge| edge.state.types.get(&value))
            .collect();
        let Some(carrier) = carriers[0].copied() else {
            return Err(domain(format!(
                "{value:?} is live at cut point {cut:?} and not defined on an edge into it"
            )));
        };
        if carriers.iter().any(|known| *known != Some(&carrier)) {
            return Err(domain(format!(
                "{value:?} is live at cut point {cut:?} and not defined at one type on every edge \
                 into it"
            )));
        }
        // Slice 17: an indexed private address is no value item.
        if edges
            .iter()
            .any(|edge| edge.state.indexed.contains_key(&value))
        {
            return Err(domain(format!(
                "{value:?} is an indexed private stack address live across cut point {cut:?} \
                 (outside the lane)"
            )));
        }
        let on_edges: Vec<Option<Closed>> = edges
            .iter()
            .map(|edge| closed_on(value, &edge.state, leaves))
            .collect();
        let frames = on_edges
            .iter()
            .filter(|on| matches!(on, Some(Closed::Frame { .. })))
            .count();
        if frames > 0 && frames < on_edges.len() {
            return Err(domain(format!(
                "{value:?} is a private stack address on some edge into cut point {cut:?} and \
                 not on another"
            )));
        }
        match &on_edges[0] {
            Some(first) if on_edges.iter().all(|on| on.as_ref() == Some(first)) => {
                closed.insert(value.0, (value, first.clone()));
            }
            Some(Closed::Frame { .. }) => {
                return Err(domain(format!(
                    "{value:?} is a different private stack address on the edges into cut point \
                     {cut:?}"
                )));
            }
            _ => {
                if edges.iter().any(|edge| edge.state.tainted.contains(&value)) {
                    tainted.insert(value.0);
                }
                items.push((value, carrier));
            }
        }
    }
    // The bytes: an item where the edges differ or hold a computed value; a
    // closed byte where every edge leaves one byte fixed for the run (its
    // stored value then closed too).
    let slots = edges[0].state.slot_bytes.len();
    let mut bytes: std::collections::BTreeMap<(u32, i64), ByteEntry> =
        std::collections::BTreeMap::new();
    for slot in 0..slots {
        for offset in 0..edges[0].state.slot_bytes[slot].len() {
            let key = (slot as u32, offset as i64);
            // Slice 17: a byte dead at the cut is left out (it starts
            // unreadable, [`CutInterface::start`]).
            if dead.contains(&key) {
                continue;
            }
            let brought: Vec<Option<SlotByte>> = edges
                .iter()
                .map(|edge| edge.state.slot_bytes[slot][offset])
                .collect();
            let earlier = previous.and_then(|previous| previous.bytes.get(&key));
            if earlier.is_none() && brought.iter().all(Option::is_none) {
                continue;
            }
            let address = FrameAddr {
                slot: key.0,
                offset: key.1,
            };
            // A byte live at the cut that an edge leaves dead (a liveness
            // error): unreadable, no claim.
            if brought.contains(&Some(SlotByte::Dead)) {
                return Err(domain(format!(
                    "cut point {cut:?} is entered on a path that leaves {} unreadable, a byte \
                     live at the cut",
                    address.describe()
                )));
            }
            if brought
                .iter()
                .any(|byte| byte.and_then(SlotByte::address).is_some())
            {
                let same = brought.iter().all(|byte| *byte == brought[0]);
                if !same || matches!(earlier, Some(ByteEntry::Input { .. })) {
                    return Err(domain(format!(
                        "cut point {cut:?} is entered on paths that leave {} holding different \
                         values, one of them a private stack address",
                        address.describe()
                    )));
                }
                bytes.insert(key, ByteEntry::Closed(brought[0].expect("an address")));
                continue;
            }
            let fixed = match (&brought[0], earlier) {
                (Some(first), None | Some(ByteEntry::Closed(_)))
                    if brought.iter().all(|byte| byte.as_ref() == Some(first))
                        && earlier.is_none_or(|known| *known == ByteEntry::Closed(*first)) =>
                {
                    let stored_closed = match first {
                        SlotByte::Stored(stored) => {
                            let on: Vec<Option<Closed>> = edges
                                .iter()
                                .map(|edge| closed_on(stored.value, &edge.state, leaves))
                                .collect();
                            match &on[0] {
                                Some(value @ (Closed::Const { .. } | Closed::Param { .. }))
                                    if on.iter().all(|known| known.as_ref() == Some(value)) =>
                                {
                                    Some((stored.value, value.clone()))
                                }
                                _ => None,
                            }
                        }
                        SlotByte::Entry { .. } => None,
                        _ => None,
                    };
                    match (first, stored_closed) {
                        (SlotByte::Stored(_), Some((value, closed_value))) => {
                            closed.entry(value.0).or_insert((value, closed_value));
                            Some(*first)
                        }
                        (SlotByte::Entry { .. }, _) => Some(*first),
                        _ => None,
                    }
                }
                _ => None,
            };
            match fixed {
                Some(byte) => {
                    bytes.insert(key, ByteEntry::Closed(byte));
                }
                None => {
                    // Slice 20 (OD-194): as a direct read takes it.
                    let readable = brought.iter().all(|byte| bool_readable(*byte));
                    let some_tainted = brought.iter().zip(edges).any(|(byte, edge)| {
                        byte.is_some_and(|byte| {
                            byte.tainted_in(&edge.state.tainted, &edge.state.tainted_sites)
                        })
                    });
                    let (bool_read, was_tainted) = match earlier {
                        Some(ByteEntry::Input { bool_read, tainted }) => (*bool_read, *tainted),
                        _ => (true, false),
                    };
                    if brought.iter().any(Option::is_none) {
                        sites.frame_byte(address);
                    }
                    bytes.insert(
                        key,
                        ByteEntry::Input {
                            bool_read: bool_read && readable,
                            tainted: was_tainted || some_tainted,
                        },
                    );
                }
            }
        }
    }
    // A byte that was closed on the edges seen in an earlier round is still
    // closed only if no edge now differs; a dropped one stays an item.
    if let Some(previous) = previous {
        for (key, entry) in &previous.bytes {
            bytes.entry(*key).or_insert_with(|| entry.clone());
        }
    }
    let mut escaped: std::collections::BTreeSet<u32> = previous
        .map(|previous| previous.escaped.clone())
        .unwrap_or_default();
    for edge in edges {
        escaped.extend(edge.state.escaped.iter().copied());
    }
    // Every closed byte's stored value is closed at the cut (an earlier
    // round's, for a byte it carried that no edge now brings again).
    let items_now: HashSet<u32> = items.iter().map(|(value, _)| value.0).collect();
    for entry in bytes.values() {
        let ByteEntry::Closed(SlotByte::Stored(stored)) = entry else {
            continue;
        };
        if closed.contains_key(&stored.value.0) {
            continue;
        }
        match previous.and_then(|previous| previous.closed.get(&stored.value.0)) {
            Some(known) if !items_now.contains(&stored.value.0) => {
                closed.insert(stored.value.0, known.clone());
            }
            _ => {
                return Err(unsupported(X86BodyUnsupported::Construction(format!(
                    "a byte carried into cut point {cut:?} stores {:?}, which is not closed there",
                    stored.value
                ))));
            }
        }
    }
    Ok(CutInterface {
        block: cut,
        region,
        items,
        params: params.len(),
        closed,
        bytes,
        tainted,
        escaped,
        dead: dead.clone(),
    })
}

/// The regions of a source cut at `cut_points` (slice 12's [`source_regions`]
/// over any cut set): one per cut point, in `cut_points` order.
pub(super) fn regions_at(cfg: &SourceCfg, cut_points: &[Block]) -> Vec<RegionCfg> {
    let cuts: HashSet<Block> = cut_points.iter().copied().collect();
    cut_points
        .iter()
        .map(|start| {
            let mut members: HashSet<Block> = HashSet::from([*start]);
            let mut work = vec![*start];
            while let Some(block) = work.pop() {
                for target in &cfg.successors[&block] {
                    if !cuts.contains(target) && members.insert(*target) {
                        work.push(*target);
                    }
                }
            }
            let order: Vec<Block> = cfg
                .order
                .iter()
                .copied()
                .filter(|block| members.contains(block))
                .collect();
            let mut predecessors: HashMap<Block, Vec<Block>> =
                order.iter().map(|block| (*block, Vec::new())).collect();
            for block in &order {
                for target in &cfg.successors[block] {
                    if !cuts.contains(target) {
                        predecessors
                            .get_mut(target)
                            .expect("a region successor is in the region")
                            .push(*block);
                    }
                }
            }
            let successors = order
                .iter()
                .map(|block| (*block, cfg.successors[block].clone()))
                .collect();
            RegionCfg {
                start: *start,
                order,
                successors,
                predecessors,
            }
        })
        .collect()
}

/// Admit a source cut at `cut_points` (slice 16): each region from its cut
/// point's interface ([`CutInterface::start`]; the entry region from the
/// function's entry), in cut-point order, then every cut's interface again
/// from every edge into it, until none grows (at most [`MAX_LOOP_ROUNDS`]).
pub(super) fn admitted_cuts(
    source: &Function,
    frame_facts: &SourceFrame,
    cfg: &SourceCfg,
    cut_points: &[Block],
    sites: &mut SourceSites,
    blamed: &mut Option<Block>,
) -> Result<LoopBody, X86BodyRefusal> {
    let region_cfgs = regions_at(cfg, cut_points);
    let cuts: HashSet<Block> = cut_points.iter().copied().collect();
    let live = live_in(source, cfg);
    // Slice 17: the bytes dead at each cut (the one byte liveness slice 12's
    // headers use too).
    let bytes_live = live_bytes(source, cfg);
    // Slice 20 (OD-192): the same liveness at every DAG join.
    let liveness = JoinLiveness::known(source, cfg, bytes_live.clone());
    let dead: HashMap<Block, std::collections::BTreeSet<(u32, i64)>> = cut_points
        .iter()
        .map(|cut| (*cut, dead_bytes(source, &bytes_live, *cut)))
        .collect();
    let leaves = leaves(source);
    let mut interfaces: std::collections::BTreeMap<Block, CutInterface> =
        std::collections::BTreeMap::new();
    let base_sites = sites.clone();
    let incoming = |regions: &[Region], cut: Block| -> Vec<CutEdge> {
        let mut edges: Vec<(usize, Block, CutEdge)> = regions
            .iter()
            .enumerate()
            .flat_map(|(q, region)| {
                region
                    .cuts
                    .iter()
                    .filter(move |((_, to), _)| *to == cut)
                    .map(move |((from, _), edge)| (q, *from, edge.clone()))
            })
            .collect();
        edges.sort_by_key(|(q, from, _)| (*q, *from));
        edges.into_iter().map(|(_, _, edge)| edge).collect()
    };
    for _ in 0..MAX_LOOP_ROUNDS {
        *sites = base_sites.clone();
        let mut merges = Vec::new();
        let mut regions: Vec<Region> = Vec::with_capacity(region_cfgs.len());
        for (index, region) in region_cfgs.iter().enumerate() {
            let start = if index == 0 {
                AdmitState::entry(frame_facts)
            } else {
                let edges = incoming(&regions, region.start);
                let previous = interfaces.get(&region.start).cloned();
                let interface = match (edges.is_empty(), previous) {
                    (true, Some(previous)) => previous,
                    (true, None) => {
                        return Err(unsupported(X86BodyUnsupported::SourceShape(format!(
                            "cut point {:?} has no edge from an earlier region",
                            region.start
                        ))));
                    }
                    (false, previous) => interface_of(
                        source,
                        region.start,
                        index,
                        &edges.iter().collect::<Vec<_>>(),
                        previous.as_ref(),
                        &live[&region.start],
                        &dead[&region.start],
                        &leaves,
                        sites,
                    )
                    .inspect_err(|_| *blamed = Some(region.start))?,
                };
                let start = interface.start(frame_facts);
                interfaces.insert(region.start, interface);
                start
            };
            let view = DagView {
                order: &region.order,
                successors: &region.successors,
                predecessors: &region.predecessors,
            };
            let (dag, cut_edges) = admitted_region(
                source,
                frame_facts,
                view,
                start,
                &cuts,
                sites,
                &mut merges,
                (index, Some(region.start)),
                &liveness,
            )?;
            regions.push(Region {
                dag,
                cuts: cut_edges,
            });
        }
        let mut grown = false;
        for (index, region) in region_cfgs.iter().enumerate().skip(1) {
            let edges = incoming(&regions, region.start);
            if edges.is_empty() {
                continue;
            }
            let previous = interfaces.get(&region.start).cloned();
            let interface = interface_of(
                source,
                region.start,
                index,
                &edges.iter().collect::<Vec<_>>(),
                previous.as_ref(),
                &live[&region.start],
                &dead[&region.start],
                &leaves,
                sites,
            )
            .inspect_err(|_| *blamed = Some(region.start))?;
            if previous.as_ref() != Some(&interface) {
                interfaces.insert(region.start, interface);
                grown = true;
            }
        }
        if !grown {
            return Ok(LoopBody {
                regions,
                headers: HashMap::new(),
                merges,
                cuts: Some(interfaces),
                in_loops: cfg
                    .loops
                    .iter()
                    .flat_map(|lp| lp.blocks.iter().copied())
                    .collect(),
            });
        }
    }
    Err(unsupported(X86BodyUnsupported::SourceShape(format!(
        "the cut interfaces do not reach a fixpoint in {MAX_LOOP_ROUNDS} rounds"
    ))))
}

// ---------------------------------------------------------------------------
// Closed terms
// ---------------------------------------------------------------------------

/// What a closed value's term is spelled in ([`closed_term`]): the function's
/// parameters and the body's source sites (whose `j`-th symbol is `sym{j}`).
#[derive(Clone, Copy)]
pub(super) struct ClosedNames<'a> {
    pub(super) params: &'a [Param],
    pub(super) sites: &'a SourceSites,
}

/// The SMT term of a closed value (no term for a private address): an
/// `Iconst`'s bits, a parameter's (as the theorem's parameter bindings state
/// it, [`parameter_term`]), a symbol's address.
pub(super) fn closed_term(
    closed: &Closed,
    params: &[Param],
    sites: &SourceSites,
) -> Result<Option<E>, X86BodyRefusal> {
    Ok(match closed {
        Closed::Const { carrier, bits } => Some(E::bv_const(*bits, carrier.bits())),
        Closed::Param { carrier, index } => {
            let param = params.get(*index).ok_or_else(|| {
                unsupported(X86BodyUnsupported::Construction(format!(
                    "closed parameter {index} is no parameter of the function"
                )))
            })?;
            Some(parameter_term(*index, param, carrier.bits()))
        }
        Closed::Symbol(symbol) => {
            let j = sites
                .symbols
                .iter()
                .position(|known| known == symbol)
                .ok_or_else(|| {
                    unsupported(X86BodyUnsupported::Construction(format!(
                        "closed symbol {} has no site",
                        symbol.describe()
                    )))
                })?;
            Some(E::var(symbol_name(j), 64))
        }
        Closed::Frame { .. } => None,
    })
}

/// The 8-bit term of a closed private byte: a byte of a stored closed value,
/// of an aggregate parameter's register, or of a stored private address.
fn closed_byte_term(
    byte: &SlotByte,
    closed: &std::collections::BTreeMap<u32, (Value, Closed)>,
    params: &[Param],
    sites: &SourceSites,
) -> Result<E, X86BodyRefusal> {
    match byte {
        SlotByte::Stored(stored) => {
            let (_, value) = closed.get(&stored.value.0).ok_or_else(|| {
                unsupported(X86BodyUnsupported::Construction(
                    "a closed byte's stored value is not closed".into(),
                ))
            })?;
            let term = closed_term(value, params, sites)?.ok_or_else(|| {
                unsupported(X86BodyUnsupported::Construction(
                    "a closed byte stores a private address as a value".into(),
                ))
            })?;
            let memory = stored.carrier.memory_value(term);
            Ok(if stored.carrier.bytes() == 1 {
                memory
            } else {
                memory.extract(8 * stored.byte + 7, 8 * stored.byte)
            })
        }
        SlotByte::Entry { root, byte } => {
            Ok(E::var(entry_name(*root), 64).extract(8 * byte + 7, 8 * byte))
        }
        SlotByte::Address { address, byte } => {
            Ok(frame_address_term(*address).extract(8 * byte + 7, 8 * byte))
        }
        _ => Err(unsupported(X86BodyUnsupported::Construction(
            "a byte that is not fixed for the run is carried as closed".into(),
        ))),
    }
}

/// The source values at the start of a cut's region (slice 16): each item its
/// free input `x{C}v{i}`, each closed value its term.
pub(super) fn start_values(
    cut: &CutInterface,
    names: ClosedNames<'_>,
) -> Result<HashMap<Value, E>, X86BodyRefusal> {
    let mut values = HashMap::new();
    for (i, (value, carrier)) in cut.items.iter().enumerate() {
        values.insert(*value, header_start_value(cut.block, i, *carrier));
    }
    for (value, closed) in cut.closed.values() {
        if let Some(term) = closed_term(closed, names.params, names.sites)? {
            values.insert(*value, term);
        }
    }
    Ok(values)
}

// ---------------------------------------------------------------------------
// The cut interface: the machine side
// ---------------------------------------------------------------------------

/// What a machine register (not paired with an item) holds at a cut (slice
/// 16), joined over the edges into it.
#[derive(Debug, Clone, PartialEq)]
enum CutReg {
    /// The same term on every edge, a function of the run's fixed inputs
    /// alone (or the same private address): carried exactly.
    Closed(ClosedReg),
    /// Defined on every edge, not closed: a read makes no claim.
    Carried,
    /// Undefined on some edge: a read is undefined.
    Absent,
}

#[derive(Debug, Clone, PartialEq)]
enum ClosedReg {
    Bits { expr: E, affine: Option<Affine> },
    Frame(FrameAddr),
}

/// The machine's assumption at one cut (slice 16): every unpaired register's
/// [`CutReg`], and the items whose register some edge leaves with bits above
/// the item's own that are not known to be zero.
#[derive(Debug, Clone, PartialEq, Default)]
pub(super) struct MachineAssumption {
    regs: Vec<(Root, CutReg)>,
    wide: std::collections::BTreeSet<usize>,
}

fn root_key(root: &Root) -> (u8, u32) {
    match root {
        Root::Physical(root) => (0, u32::from(*root)),
        Root::Virtual(id) => (1, *id),
    }
}

/// Whether `name` is a free input or definition fixed for the whole run: an
/// entry register or incoming stack eightbyte, a symbol's address, a slot's
/// address, a frame byte's initial value, a `bool` parameter's caller view,
/// or a parameter binding. OD-233's definitions exclude a slot's address
/// (`build_theorem`'s check K1).
pub(super) fn fixed_for_the_run(name: &str) -> bool {
    let numbered = |prefix: &str| {
        name.strip_prefix(prefix)
            .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
    };
    name.starts_with("e_")
        || ["sym", "slot", "f", "a", "z", "p"]
            .iter()
            .any(|prefix| numbered(prefix))
}

/// Slice 20 (ruling OD-194): the undefined-bits inputs (`u{k}`, `w{k}`:
/// [`MachineNames::undefined`]) that a row outside every natural loop of the
/// source introduces (`in_loops`, the loops' LIR blocks; a row of a dispatch
/// block counts as its owner's). Such a row runs at most once in a run, so
/// the input names one value for the whole run, a closed leaf like an entry
/// value ([`fixed_for_the_run`]); one a loop row introduces may differ from
/// one visit of the row to the next and stays carried.
fn fixed_undefined(
    names: &MachineNames,
    in_loops: &std::collections::BTreeSet<Block>,
    cfg: &MachineCfg<'_>,
    correspondence: &Correspondence,
) -> HashSet<String> {
    let mut fixed = HashSet::new();
    for (site, expr) in &names.undefined_at {
        let UndefinedSite::Row(ordinal) = site;
        let Some(block) = cfg.machine.block_order.iter().find(|block| {
            let first = cfg.ordinals[*block];
            (first..first + cfg.machine.blocks[*block].insts.len()).contains(ordinal)
        }) else {
            continue;
        };
        let owner = correspondence.dispatch.get(block).unwrap_or(block);
        let Some(lir) = correspondence.origin.get(owner) else {
            continue;
        };
        if in_loops.contains(lir) {
            continue;
        }
        if let E::Var { name, .. } = expr {
            fixed.insert(name.clone());
        }
    }
    fixed
}

/// The most nodes a carried closed machine term, or a defined cut input's
/// term (OD-233), may have.
const MAX_CLOSED_TERM_NODES: usize = 64;

/// The number of nodes of `expr` as a tree, counting at most `limit + 1`.
fn tree_nodes(expr: &E, limit: usize) -> usize {
    let mut nodes = 0usize;
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        nodes += 1;
        if nodes > limit {
            return nodes;
        }
        node.for_each_child(&mut |child| stack.push(child));
    }
    nodes
}

/// `expr` with every name `defs` defines replaced by its term, recursively,
/// when the result names only inputs fixed for the run ([`fixed_for_the_run`],
/// and `fixed`'s: slice 20's undefined-bits inputs, [`fixed_undefined`]) and
/// has at most [`MAX_CLOSED_TERM_NODES`] nodes; else `None`. A name
/// [`fixed_for_the_run`] accepts is kept, defined or not. `defs` are the
/// machine's definitions for a closed register ([`machine_assumption`]), or
/// the statement's source definitions and the chosen cut inputs' terms for a
/// defined cut input (OD-233, [`cut_definitions`]). `memo` holds each name's
/// resolution under the same definitions. The names `expr` reaches are
/// resolved deepest first on an explicit stack (a source definition chain
/// may be thousands of definitions deep).
fn run_fixed_term(
    expr: &E,
    defs: &HashMap<&str, &E>,
    fixed: &HashSet<String>,
    memo: &mut HashMap<String, Option<E>>,
) -> Option<E> {
    let open = |var: &str| !fixed_for_the_run(var) && !fixed.contains(var);
    // Each name on the stack is resolved once every name its definition
    // reads is (`true`: those are pushed above it). A cycle cannot occur
    // (each definition reads earlier ones only); a name met again before it
    // is resolved resolves to `None`, which bounds a malformed one.
    let mut pending: HashSet<String> = HashSet::new();
    let mut stack: Vec<(String, bool)> = expr
        .free_vars()
        .into_iter()
        .filter(|var| open(var))
        .map(|var| (var, false))
        .collect();
    while let Some((name, read)) = stack.pop() {
        if memo.contains_key(&name) {
            continue;
        }
        let Some(def) = defs.get(name.as_str()) else {
            memo.insert(name, None);
            continue;
        };
        if read {
            let resolved = substituted_term(def, fixed, memo);
            pending.remove(&name);
            memo.insert(name, resolved);
            continue;
        }
        if !pending.insert(name.clone()) {
            memo.insert(name, None);
            continue;
        }
        let reads: Vec<String> = def
            .free_vars()
            .into_iter()
            .filter(|var| open(var) && !memo.contains_key(var))
            .collect();
        stack.push((name, true));
        stack.extend(reads.into_iter().map(|var| (var, false)));
    }
    substituted_term(expr, fixed, memo)
}

/// `expr` with each name it reads that is not fixed for the run replaced by
/// its resolution in `memo` ([`run_fixed_term`]), when every such name has
/// one and the result has at most [`MAX_CLOSED_TERM_NODES`] nodes.
fn substituted_term(
    expr: &E,
    fixed: &HashSet<String>,
    memo: &HashMap<String, Option<E>>,
) -> Option<E> {
    let mut env: HashMap<String, E> = HashMap::new();
    for var in expr.free_vars() {
        if fixed_for_the_run(&var) || fixed.contains(&var) {
            continue;
        }
        env.insert(var.clone(), memo.get(&var).cloned().flatten()?);
    }
    let term = if env.is_empty() {
        expr.clone()
    } else {
        expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
            Ok(match node {
                E::Var { name, .. } => env.get(name).cloned(),
                _ => None,
            })
        })
        .unwrap_or_else(|never| match never {})
        .unwrap_or_else(|| expr.clone())
    };
    (tree_nodes(&term, MAX_CLOSED_TERM_NODES) <= MAX_CLOSED_TERM_NODES).then_some(term)
}

/// The machine assumption at cut `cut` from the machine states at the end of
/// the edges into it (`exits`) joined with an earlier round's (`previous`):
/// a register closed on every edge stays closed, else carried, and absent
/// where some edge leaves it undefined; an item is wide once some edge
/// leaves its register with bits above its own not known to be zero. An
/// outgoing argument area open on an edge, a slot the machine lets escape
/// where the source does not, a byte the machine writes that the cut does not
/// relate, a stored private address the cut does not carry, or an item's
/// register holding no bits on an edge make no claim.
fn machine_assumption(
    cut: &CutInterface,
    roots: &[ParamRoot],
    exits: &[(Block, &MachineState)],
    previous: Option<&MachineAssumption>,
    names: &MachineNames,
    fixed: &HashSet<String>,
) -> Result<MachineAssumption, X86BodyRefusal> {
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    let block = cut.block;
    let defs: HashMap<&str, &E> = names
        .definitions
        .iter()
        .map(|(name, expr, _)| (name.as_str(), expr))
        .collect();
    let mut memo: HashMap<String, Option<E>> = HashMap::new();
    for (from, exit) in exits {
        if exit.outgoing.is_some() {
            return Err(no_claim(format!(
                "the machine enters cut point {block:?} from block {from:?} with an outgoing \
                 argument area open"
            )));
        }
        if let Some(slot) = exit.escaped.iter().find(|slot| !cut.escaped.contains(slot)) {
            return Err(no_claim(format!(
                "the machine lets private stack slot {slot} escape on the edge from block {from:?} \
                 into cut point {block:?}, where its LIR source does not"
            )));
        }
        for (slot, bytes) in exit.stack.iter().enumerate() {
            for (offset, byte) in bytes.iter().enumerate() {
                let key = (slot as u32, offset as i64);
                // Slice 17: a byte dead at the cut is neither related nor
                // checked.
                if cut.dead.contains(&key) {
                    continue;
                }
                // A related byte an edge leaves unreadable makes no claim.
                if cut.bytes.contains_key(&key) && byte.as_ref().is_some_and(|byte| byte.dead) {
                    return Err(no_claim(format!(
                        "the machine leaves private stack slot {slot} byte {offset} unreadable on \
                         the edge from block {from:?} into cut point {block:?}"
                    )));
                }
                match (cut.bytes.get(&key), byte) {
                    (None, None) => {}
                    (None, Some(_)) => {
                        return Err(no_claim(format!(
                            "the machine writes private stack slot {slot} byte {offset} on the \
                             edge from block {from:?} into cut point {block:?}, which its LIR \
                             source does not"
                        )));
                    }
                    (
                        Some(ByteEntry::Closed(SlotByte::Address {
                            address,
                            byte: index,
                        })),
                        _,
                    ) => {
                        if !byte
                            .as_ref()
                            .is_some_and(|byte| byte.frame == Some(*address) && byte.byte == *index)
                        {
                            return Err(no_claim(format!(
                                "the machine leaves private stack slot {slot} byte {offset} other \
                                 than the stored private address its LIR source carries into cut \
                                 point {block:?} from block {from:?}"
                            )));
                        }
                    }
                    (Some(_), Some(byte)) if byte.frame.is_some() => {
                        return Err(no_claim(format!(
                            "the machine leaves a private stack address in slot {slot} byte \
                             {offset} on the edge from block {from:?} into cut point {block:?}, \
                             where its LIR source does not"
                        )));
                    }
                    (Some(_), _) => {}
                }
            }
        }
    }
    let paired: HashSet<Root> = roots.iter().flat_map(|root| root.roots()).collect();
    let mut keys: Vec<Root> = exits
        .iter()
        .flat_map(|(_, exit)| exit.regs.keys().copied())
        .chain(
            previous
                .into_iter()
                .flat_map(|known| known.regs.iter().map(|(root, _)| *root)),
        )
        .filter(|root| !paired.contains(root))
        .collect();
    keys.sort_unstable_by_key(root_key);
    keys.dedup();
    let mut regs: Vec<(Root, CutReg)> = Vec::with_capacity(keys.len());
    for root in keys {
        let on_edges: Vec<CutReg> = exits
            .iter()
            .map(|(_, exit)| match exit.regs.get(&root) {
                None => CutReg::Absent,
                Some(RegValue::Frame(address)) => CutReg::Closed(ClosedReg::Frame(*address)),
                Some(RegValue::Bits(slot)) => {
                    match run_fixed_term(&slot.expr, &defs, fixed, &mut memo) {
                        Some(expr) => CutReg::Closed(ClosedReg::Bits {
                            expr,
                            affine: slot.affine,
                        }),
                        None => CutReg::Carried,
                    }
                }
                Some(
                    RegValue::Mixed
                    | RegValue::Carried
                    | RegValue::Dispatch(_)
                    | RegValue::Indexed(_),
                ) => CutReg::Carried,
            })
            .chain(previous.and_then(|known| {
                known
                    .regs
                    .iter()
                    .find(|(known, _)| *known == root)
                    .map(|(_, reg)| reg.clone())
            }))
            .collect();
        let joined = on_edges
            .into_iter()
            .reduce(|a, b| match (a, b) {
                (CutReg::Absent, _) | (_, CutReg::Absent) => CutReg::Absent,
                (CutReg::Carried, _) | (_, CutReg::Carried) => CutReg::Carried,
                (CutReg::Closed(ClosedReg::Frame(a)), CutReg::Closed(ClosedReg::Frame(b)))
                    if a == b =>
                {
                    CutReg::Closed(ClosedReg::Frame(a))
                }
                (
                    CutReg::Closed(ClosedReg::Bits { expr: a, affine: x }),
                    CutReg::Closed(ClosedReg::Bits { expr: b, affine: y }),
                ) if a == b => CutReg::Closed(ClosedReg::Bits {
                    expr: a,
                    affine: if x == y { x } else { None },
                }),
                _ => CutReg::Carried,
            })
            .unwrap_or(CutReg::Absent);
        regs.push((root, joined));
    }
    let mut wide = previous.map(|known| known.wide.clone()).unwrap_or_default();
    for (i, root) in roots.iter().enumerate() {
        if root.value_bits >= 64 || wide.contains(&i) {
            continue;
        }
        let clean = exits.iter().all(|(_, exit)| {
            matches!(
                exit.regs.get(&root.root),
                Some(RegValue::Bits(slot)) if zero_above(&slot.expr, root.value_bits, &defs)
            )
        });
        if !clean {
            wide.insert(i);
        }
    }
    Ok(MachineAssumption { regs, wide })
}

/// The machine state at the start of a cut's region (slice 16): each item's
/// register its template ([`ParamRoot::template`], or the clean one when no
/// edge leaves bits above it), every other register as the assumption says
/// ([`CutReg`]), each byte item the shared free input, each closed byte its
/// term (a stored private address tracked as such), the source's escaped
/// slots, no flags, no outgoing area, and nothing stopped.
#[allow(clippy::too_many_arguments)]
fn machine_cut_start(
    cut: &CutInterface,
    roots: &[ParamRoot],
    assumption: &MachineAssumption,
    convention: BoolArguments,
    slot_sizes: &[u32],
    params: &[Param],
    sites: &SourceSites,
) -> Result<MachineState, X86BodyRefusal> {
    let mut regs: HashMap<Root, RegValue> = HashMap::new();
    for (root, reg) in &assumption.regs {
        match reg {
            CutReg::Closed(ClosedReg::Bits { expr, affine }) => {
                regs.insert(
                    *root,
                    RegValue::Bits(Slot {
                        expr: expr.clone(),
                        affine: *affine,
                    }),
                );
            }
            CutReg::Closed(ClosedReg::Frame(address)) => {
                regs.insert(*root, RegValue::Frame(*address));
            }
            CutReg::Carried => {
                regs.insert(*root, RegValue::Carried);
            }
            CutReg::Absent => {}
        }
    }
    for (i, root) in roots.iter().enumerate() {
        let expr = if assumption.wide.contains(&i) {
            root.template(cut.block, i, convention)
        } else {
            root.clean_template(cut.block, i)
        };
        regs.insert(root.root, RegValue::Bits(Slot { expr, affine: None }));
        // Slice 20 (OD-193): an `I128`'s high register, its high half.
        if let Some((high, expr)) = root.high_template(cut.block, i) {
            regs.insert(high, RegValue::Bits(Slot { expr, affine: None }));
        }
    }
    let mut stack: Vec<Vec<Option<MachineByte>>> = slot_sizes
        .iter()
        .map(|size| vec![None; *size as usize])
        .collect();
    for (&(slot, offset), entry) in &cut.bytes {
        let address = FrameAddr { slot, offset };
        stack[slot as usize][offset as usize] = Some(match entry {
            ByteEntry::Input { .. } => MachineByte {
                term: E::var(header_byte_name(cut.block, address), 8),
                width: 8,
                byte: 0,
                affine: None,
                frame: None,
                dead: false,
            },
            ByteEntry::Closed(SlotByte::Address {
                address: stored,
                byte,
            }) => MachineByte {
                term: frame_address_term(*stored),
                width: 64,
                byte: *byte,
                affine: None,
                frame: Some(*stored),
                dead: false,
            },
            ByteEntry::Closed(byte) => MachineByte {
                term: closed_byte_term(byte, &cut.closed, params, sites)?,
                width: 8,
                byte: 0,
                affine: None,
                frame: None,
                dead: false,
            },
        });
    }
    // Slice 17: a byte dead at the cut starts unreadable.
    for &(slot, offset) in &cut.dead {
        stack[slot as usize][offset as usize] = Some(MachineByte::dead());
    }
    let mut escaped = std::collections::BTreeSet::new();
    escape_machine(
        &mut escaped,
        &stack,
        cut.escaped.iter().copied().collect::<Vec<_>>(),
    );
    Ok(MachineState {
        regs,
        stack,
        escaped,
        flags: Flags::Unmodelled,
        outgoing: None,
        stopped: bit_zero(),
        trapped: bit_zero(),
    })
}

/// The machine register of each item of each cut (slice 16; as slice 12's
/// [`loop_pairing`]): for a parameter of the cut block, the register the last
/// row stamped with its copy on an edge into the cut writes (the first edge,
/// in region and block order, that has such a row); for any other value, the
/// register the last row stamped with its LIR definition writes (for another
/// block's parameter, one of its edge copies, the first in block order that
/// has such a row). The
/// stamps only CHOOSE the register: the relation is stated on every edge into
/// the cut, so a wrong choice is refuted or makes no claim. A value with no
/// such row, a physical, callee-saved or too narrow register, or two items in
/// one register make no claim.
pub(super) fn cut_pairing(
    source: &Function,
    loops: &LoopBody,
    cuts: &std::collections::BTreeMap<Block, CutInterface>,
    cfg: &MachineCfg<'_>,
    correspondence: &Correspondence,
) -> Result<HashMap<Block, Vec<ParamRoot>>, X86BodyRefusal> {
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    // Every LIR instruction that defines each value: one, or (a block
    // parameter) each edge copy into its block.
    let mut definitions: HashMap<Value, Vec<(Block, usize)>> = HashMap::new();
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for block in blocks {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            for result in &inst.results {
                definitions
                    .entry(*result)
                    .or_default()
                    .push((*block, index));
            }
        }
    }
    // The register the last row stamped with LIR instruction `(lir, index)`
    // writes, of at least `bits` bits (an instruction with two results, an
    // `add` and its overflow `setb`, writes each into a register of its
    // own); else the last one's.
    // Slice 24c (OD-228): `lowering`, never the segment's machine block: a
    // copy that runs inside a segment makes no claim here.
    let lowered_for = |lir: Block| -> Option<Block> {
        if mutated("s24c-cut-pairing-machine-of") {
            correspondence.machine_of(lir)
        } else {
            correspondence.lowering.get(&lir).copied()
        }
    };
    let register_of = |lir: Block, index: usize, bits: u32| -> Option<Reg> {
        let lowered = &lowered_for(lir)?;
        let stamp = trust_cg_ir::provenance::SourceInstId {
            block: lir.0,
            index: index as u32,
        };
        let written: Vec<Reg> = cfg.machine.blocks[lowered]
            .insts
            .iter()
            .rev()
            .filter(|inst| inst.lowering_provenance.source_id() == Some(stamp))
            .filter_map(destination_reg)
            .collect();
        written
            .iter()
            .find(|reg| reg.bits >= bits)
            .or(written.first())
            .copied()
    };
    // Slice 20 (OD-193): the pair of 64-bit registers the rows stamped with
    // LIR instruction `(lir, index)` write ([`i128_pair`]).
    let pair_of = |lir: Block, index: usize| -> Option<(Reg, Reg)> {
        let lowered = &lowered_for(lir)?;
        let stamp = trust_cg_ir::provenance::SourceInstId {
            block: lir.0,
            index: index as u32,
        };
        let stamped: Vec<&X86ISelInst> = cfg.machine.blocks[lowered]
            .insts
            .iter()
            .filter(|inst| inst.lowering_provenance.source_id() == Some(stamp))
            .collect();
        i128_pair(&stamped)
    };
    let mut pairing = HashMap::new();
    for (block, cut) in cuts {
        let mut edges: Vec<(usize, Block, &CutEdge)> = loops
            .regions
            .iter()
            .enumerate()
            .flat_map(|(q, region)| {
                region
                    .cuts
                    .iter()
                    .filter(|((_, to), _)| to == block)
                    .map(move |((from, _), edge)| (q, *from, edge))
            })
            .collect();
        edges.sort_by_key(|(q, from, _)| (*q, *from));
        let mut roots: Vec<ParamRoot> = Vec::with_capacity(cut.items.len());
        for (i, (value, carrier)) in cut.items.iter().enumerate() {
            let wanted = carrier.bits();
            // Slice 20 (ruling OD-193): an `I128` item is the pair of 64-bit
            // registers its stamped rows write ([`i128_pair`]).
            if *carrier == Carrier::I128 {
                let pair = if i < cut.params {
                    edges.iter().find_map(|(_, from, edge)| {
                        edge.copies[i].and_then(|index| pair_of(*from, index))
                    })
                } else {
                    definitions
                        .get(value)
                        .and_then(|at| at.iter().find_map(|(lir, index)| pair_of(*lir, *index)))
                };
                let Some((low, high)) = pair else {
                    return Err(no_claim(format!(
                        "no two virtual 64-bit registers hold the i128 {value:?}, live across cut \
                         point {block:?}"
                    )));
                };
                if roots.iter().any(|known| {
                    known
                        .roots()
                        .any(|known| known == low.root || known == high.root)
                }) {
                    return Err(no_claim(format!(
                        "two values live across cut point {block:?} are held in {} or {}",
                        low.root.describe(),
                        high.root.describe()
                    )));
                }
                roots.push(ParamRoot {
                    root: low.root,
                    high: Some(high.root),
                    value_bits: 128,
                    bits: 64,
                });
                continue;
            }
            let reg = if i < cut.params {
                edges.iter().find_map(|(_, from, edge)| {
                    edge.copies[i].and_then(|index| register_of(*from, index, wanted))
                })
            } else {
                definitions.get(value).and_then(|at| {
                    at.iter()
                        .find_map(|(lir, index)| register_of(*lir, *index, wanted))
                })
            };
            let Some(reg) = reg else {
                return Err(no_claim(format!(
                    "no machine row writes a register as the definition of {value:?}, live across \
                     cut point {block:?}"
                )));
            };
            // A `bool` is stated as the backend's clean 32-bit carrier, or as
            // its byte when an 8-bit register holds it (a `setcc`'s): the
            // register's bits above are free either way.
            let bits = match carrier.bits() {
                1 if reg.bits < 32 => 8,
                1 => 32,
                bits => bits,
            };
            if let Root::Physical(physical) = reg.root {
                return Err(no_claim(format!(
                    "{value:?}, live across cut point {block:?}, is held in physical register {}",
                    root_name(physical)
                )));
            }
            if reg.bits < bits {
                return Err(no_claim(format!(
                    "{value:?}, live across cut point {block:?}, is held in a {}-bit register",
                    reg.bits
                )));
            }
            if roots
                .iter()
                .any(|known| known.roots().any(|known| known == reg.root))
            {
                return Err(no_claim(format!(
                    "two values live across cut point {block:?} are held in {}",
                    reg.root.describe()
                )));
            }
            roots.push(ParamRoot {
                root: reg.root,
                high: None,
                value_bits: carrier.bits(),
                bits,
            });
        }
        pairing.insert(*block, roots);
    }
    Ok(pairing)
}

/// Walk a source cut at its cut points under one caller convention (slice
/// 16), region by region in cut-point order, each from its cut point's
/// machine start ([`machine_cut_start`]; the entry region from the machine's
/// entry), then every cut's machine assumption again from every edge into it,
/// until none grows (at most [`MAX_LOOP_ROUNDS`]). Returns each region's
/// walks.
#[allow(clippy::too_many_arguments)]
pub(super) fn walk_cuts(
    loops: &LoopBody,
    cuts: &std::collections::BTreeMap<Block, CutInterface>,
    sites: &SourceSites,
    cfg: &MachineCfg<'_>,
    correspondence: &Correspondence,
    pairing: &HashMap<Block, Vec<ParamRoot>>,
    names: &mut MachineNames,
    frame_bytes: &mut Vec<FrameAddr>,
) -> Result<Vec<RegionWalk>, X86BodyRefusal> {
    let no_claim = |detail: String| unsupported(X86BodyUnsupported::MachineFunction(detail));
    let base_names = names.clone();
    let base_frame_bytes = frame_bytes.clone();
    let mut assumptions: std::collections::BTreeMap<Block, MachineAssumption> =
        std::collections::BTreeMap::new();
    let params = &loops.regions[0].dag.blocks[&loops.regions[0].dag.order[0]].params;
    let edges_into = |walks: &[RegionWalk], cut: Block| -> Vec<(Block, MachineState)> {
        let mut edges: Vec<(usize, Block, MachineState)> = walks
            .iter()
            .enumerate()
            .flat_map(|(q, walk)| {
                walk.2
                    .iter()
                    .filter(move |((_, to), _)| *to == cut)
                    .map(move |((from, _), exit)| (q, *from, exit.clone()))
            })
            .collect();
        edges.sort_by_key(|(q, from, _)| (*q, *from));
        edges
            .into_iter()
            .map(|(_, from, exit)| (from, exit))
            .collect()
    };
    for _ in 0..MAX_LOOP_ROUNDS {
        *names = base_names.clone();
        *frame_bytes = base_frame_bytes.clone();
        let mut walks: Vec<RegionWalk> = Vec::with_capacity(loops.regions.len());
        for (index, region) in loops.regions.iter().enumerate() {
            let first = region.dag.order[0];
            let (start, entry_facts) = match cuts.get(&first) {
                None => {
                    check_machine_entry(cfg, correspondence, first)?;
                    let (initial, entry_names, abi_views) =
                        MachineState::entry(&region.dag.blocks[&first], names.convention);
                    (initial, Some((entry_names, abi_views)))
                }
                Some(cut) => {
                    let exits = edges_into(&walks, first);
                    let previous = assumptions.get(&first).cloned();
                    let assumption = match (exits.is_empty(), previous) {
                        (true, Some(previous)) => previous,
                        (true, None) => {
                            return Err(no_claim(format!(
                                "cut point {first:?} has no machine edge from an earlier region"
                            )));
                        }
                        (false, previous) => machine_assumption(
                            cut,
                            &pairing[&first],
                            &exits
                                .iter()
                                .map(|(from, exit)| (*from, exit))
                                .collect::<Vec<_>>(),
                            previous.as_ref(),
                            names,
                            &fixed_undefined(names, &loops.in_loops, cfg, correspondence),
                        )?,
                    };
                    let start = machine_cut_start(
                        cut,
                        &pairing[&first],
                        &assumption,
                        names.convention,
                        &region.dag.blocks[&first].slot_sizes,
                        params,
                        sites,
                    )?;
                    assumptions.insert(first, assumption);
                    (start, None)
                }
            };
            debug_assert!(index > 0 || entry_facts.is_some());
            let mut walk = walk_region(
                &region.dag,
                sites,
                cfg,
                correspondence,
                names,
                frame_bytes,
                start,
            )?;
            if let Some((entry_names, abi_views)) = entry_facts {
                let entry_walk = walk.0.get_mut(&first).expect("the entry block is walked");
                entry_walk.entry_names = entry_names;
                entry_walk.abi_views = abi_views;
            }
            walks.push(walk);
        }
        let mut grown = false;
        for (block, cut) in cuts {
            let exits = edges_into(&walks, *block);
            let previous = assumptions.get(block).cloned();
            let assumption = machine_assumption(
                cut,
                &pairing[block],
                &exits
                    .iter()
                    .map(|(from, exit)| (*from, exit))
                    .collect::<Vec<_>>(),
                previous.as_ref(),
                names,
                &fixed_undefined(names, &loops.in_loops, cfg, correspondence),
            )?;
            if previous.as_ref() != Some(&assumption) {
                assumptions.insert(*block, assumption);
                grown = true;
            }
        }
        if grown {
            continue;
        }
        // The fixpoint: each item's register holds bits on every edge into
        // its cut, and every unwritten byte the relation reads is registered.
        for (block, cut) in cuts {
            for (from, exit) in edges_into(&walks, *block) {
                for (root, (value, _)) in pairing[block].iter().zip(&cut.items) {
                    for held in root.roots() {
                        if !matches!(exit.regs.get(&held), Some(RegValue::Bits(_))) {
                            return Err(no_claim(format!(
                                "{} holds no value on the edge from block {from:?} into cut \
                                 point {block:?}, where it holds {value:?}",
                                held.describe()
                            )));
                        }
                    }
                }
                for &(slot, offset) in cut.bytes.keys() {
                    if exit.stack[slot as usize][offset as usize].is_none() {
                        register_frame_byte(frame_bytes, FrameAddr { slot, offset });
                    }
                }
            }
        }
        return Ok(walks);
    }
    Err(no_claim(format!(
        "the cut points' machine assumptions do not reach a fixpoint in {MAX_LOOP_ROUNDS} rounds"
    )))
}

// ---------------------------------------------------------------------------
// The relation on a cut edge
// ---------------------------------------------------------------------------

/// The cut-point relation on one edge (slice 16), and OD-233's claims of
/// the cut's defined inputs on it.
pub(super) struct CutRelation {
    /// The relation as `(source, machine)` pairs ([`split_relation`]).
    pub(super) pairs: Vec<(E, E)>,
    /// OD-233: each defined input of the cut as `(name, its source term on the
    /// edge, the name as a term)`, in [`CutDefined::named`] order: the claim
    /// that the edge brings the input's definition. The source term is the
    /// one [`Self::pairs`] states for the input on the edge (an item's whole
    /// value; a byte's source byte, of its run's source term).
    pub(super) definitions: Vec<(String, E, E)>,
}

/// The cut-point relation of `cut` on one edge into it (slice 16), as
/// `(source, machine)` pairs under each caller convention walked: each item's
/// value on the edge (a parameter of the cut its edge copy's value) against
/// the low bits of its register ([`ParamRoot::relation`]), then each byte of
/// the interface, the source's byte on the edge against the machine's at the
/// same frame address. Each closed value's term on the edge must be the term
/// the cut carries (else no claim: the cut would carry a value some edge does
/// not bring). OD-233: and, once per edge (the source term is the same under
/// every caller convention), each input `defined` defines, the source term
/// this relation states for it on the edge (an item's value; a byte's source
/// byte, of its run's term) paired with its name; an input the relation
/// states no term for gets no pair (and `build_theorem`'s check K2 refuses).
#[allow(clippy::too_many_arguments)]
pub(super) fn split_relation(
    cut: &CutInterface,
    roots: &[ParamRoot],
    edge: &CutEdge,
    exits: &(MachineState, Option<MachineState>),
    values: &HashMap<Value, E>,
    walks: &BodyWalks,
    names: ClosedNames<'_>,
    defined: Option<&CutDefined>,
) -> Result<CutRelation, X86BodyRefusal> {
    let construction = |detail: String| unsupported(X86BodyUnsupported::Construction(detail));
    for (value, closed) in cut.closed.values() {
        let Some(term) = closed_term(closed, names.params, names.sites)? else {
            continue;
        };
        if values.get(value) != Some(&term) {
            return Err(construction(format!(
                "{value:?}, carried closed into cut point {:?}, is another term on an edge into it",
                cut.block
            )));
        }
    }
    let mut pairs = Vec::new();
    // OD-233: the relation's own source term of each input `defined`
    // defines, under the first convention walked (the source side is the
    // same under each): an item's value on the edge, and a byte's source
    // byte, whose concatenation over its run is the run's source term (the
    // run's one whole store when its bytes are exactly that store's).
    let mut item_sources: std::collections::BTreeMap<usize, E> = Default::default();
    let mut byte_sources: std::collections::BTreeMap<(u32, i64), E> = Default::default();
    let walked = std::iter::once((&exits.0, BoolArguments::PsAbi))
        .chain(exits.1.as_ref().map(|exit| (exit, BoolArguments::Clean32)));
    for (walk, (exit, convention)) in walked.enumerate() {
        for (i, ((value, _), root)) in cut.items.iter().zip(roots).enumerate() {
            let on_edge = if i < cut.params {
                edge.values[i]
            } else {
                *value
            };
            let source = values.get(&on_edge).cloned().ok_or_else(|| {
                construction(format!(
                    "{on_edge:?} has no term on an edge into cut point {:?}",
                    cut.block
                ))
            })?;
            if walk == 0 && defined.is_some_and(|defined| defined.items.contains_key(&i)) {
                item_sources.insert(i, source.clone());
            }
            let bits_of = |held: Root| match exit.regs.get(&held) {
                Some(RegValue::Bits(register)) => Ok(register.expr.clone()),
                _ => Err(construction(format!(
                    "{} holds no bits on an edge into cut point {:?}",
                    held.describe(),
                    cut.block
                ))),
            };
            let register = bits_of(root.root)?;
            // Slice 20 (OD-193): an `I128`'s high register too.
            let high = root.high.map(bits_of).transpose()?;
            pairs.extend(root.relations(source, register, high, convention));
        }
        // The bytes in runs within one 8-byte chunk of a slot (slice 7's
        // `slot_chunks`): a run's two sides are its bytes concatenated, low
        // byte first, or the one store whose bytes it is exactly. Equal
        // exactly when each byte is.
        let value = |v: &Value| values[v].clone();
        let mut runs: Vec<Vec<(u32, i64)>> = Vec::new();
        for &key in cut.bytes.keys() {
            match runs.last_mut() {
                Some(run)
                    if run.last().is_some_and(|last| {
                        last.0 == key.0 && last.1 + 1 == key.1 && last.1 / 8 == key.1 / 8
                    }) =>
                {
                    run.push(key)
                }
                _ => runs.push(vec![key]),
            }
        }
        for run in runs {
            let source_part: Vec<Option<SlotByte>> = run
                .iter()
                .map(|(slot, offset)| edge.state.slot_bytes[*slot as usize][*offset as usize])
                .collect();
            if walk == 0
                && let Some(defined) = defined
            {
                for (&(slot, offset), byte) in run.iter().zip(&source_part) {
                    if defined.bytes.contains_key(&(slot, offset)) {
                        byte_sources.insert(
                            (slot, offset),
                            source_slot_byte(FrameAddr { slot, offset }, byte, &value, walks),
                        );
                    }
                }
            }
            let source = source_whole_store(&source_part, &value).unwrap_or_else(|| {
                concat_bytes(
                    run.iter()
                        .zip(&source_part)
                        .map(|((slot, offset), byte)| {
                            source_slot_byte(
                                FrameAddr {
                                    slot: *slot,
                                    offset: *offset,
                                },
                                byte,
                                &value,
                                walks,
                            )
                        })
                        .collect(),
                )
            });
            let machine_part: Vec<Option<MachineByte>> = run
                .iter()
                .map(|(slot, offset)| exit.stack[*slot as usize][*offset as usize].clone())
                .collect();
            let machine = machine_whole_store(&machine_part).unwrap_or_else(|| {
                concat_bytes(
                    run.iter()
                        .zip(&machine_part)
                        .map(|((slot, offset), byte)| match byte {
                            Some(byte) => byte.expr(),
                            None => E::var(
                                frame_byte_name(walks.frame_byte(FrameAddr {
                                    slot: *slot,
                                    offset: *offset,
                                })),
                                8,
                            ),
                        })
                        .collect(),
                )
            });
            pairs.push((source, machine));
        }
    }
    let mut definitions = Vec::new();
    if let Some(defined) = defined {
        for (i, term) in &defined.items {
            if let Some(source) = item_sources.remove(i) {
                let name = header_value_name(cut.block, *i);
                let var = E::var(name.clone(), term.bv_width());
                definitions.push((name, source, var));
            }
        }
        for &(slot, offset) in defined.bytes.keys() {
            if let Some(source) = byte_sources.remove(&(slot, offset)) {
                let name = header_byte_name(cut.block, FrameAddr { slot, offset });
                let var = E::var(name.clone(), 8);
                definitions.push((name, source, var));
            }
        }
    }
    Ok(CutRelation { pairs, definitions })
}

// ---------------------------------------------------------------------------
// Defined cut inputs (ruling OD-233)
// ---------------------------------------------------------------------------

/// OD-233: the inputs of one cut point that every edge into it brings as one
/// term over the run's fixed inputs ([`run_fixed_term`]), and those terms.
#[derive(Debug, Clone, Default, PartialEq)]
pub(super) struct CutDefined {
    /// Value item index -> its term, at the item's carrier width (never
    /// `I128`).
    pub(super) items: std::collections::BTreeMap<usize, E>,
    /// Byte item `(slot, offset)` -> its 8-bit term.
    pub(super) bytes: std::collections::BTreeMap<(u32, i64), E>,
}

impl CutDefined {
    fn is_empty(&self) -> bool {
        self.items.is_empty() && self.bytes.is_empty()
    }

    /// Each defined input of cut point `cut` as `(name, term)`, its items
    /// ([`header_value_name`]) then its bytes ([`header_byte_name`]).
    pub(super) fn named(&self, cut: Block) -> Vec<(String, &E)> {
        self.items
            .iter()
            .map(|(i, term)| (header_value_name(cut, *i), term))
            .chain(self.bytes.iter().map(|(&(slot, offset), term)| {
                (header_byte_name(cut, FrameAddr { slot, offset }), term)
            }))
            .collect()
    }
}

/// OD-233: every cut point's [`CutDefined`]; empty off the parts route. One
/// value feeds the statement's definitions, the claims on every edge, the
/// check that every edge carries them and the free-input list.
#[derive(Debug, Clone, Default)]
pub(super) struct CutDefinitions {
    pub(super) by_cut: std::collections::BTreeMap<Block, CutDefined>,
}

impl CutDefinitions {
    /// The definitions the statement makes, by cut point, each cut's items
    /// then its bytes.
    pub(super) fn definitions(&self) -> Vec<(String, E)> {
        self.by_cut
            .iter()
            .flat_map(|(cut, defined)| {
                defined
                    .named(*cut)
                    .into_iter()
                    .map(|(name, term)| (name, term.clone()))
            })
            .collect()
    }

    /// [`Self::definitions`] as the statement states them. Tests only
    /// (`od233-forge`): the first defined byte's term off by one, in its
    /// definition alone (a wrong choice, which its edge's claim refutes).
    pub(super) fn stated(&self) -> Vec<(String, E)> {
        let mut definitions = self.definitions();
        if mutated("od233-forge")
            && let Some((cut, defined)) = self
                .by_cut
                .iter()
                .find(|(_, defined)| !defined.bytes.is_empty())
        {
            let (&(slot, offset), _) = defined.bytes.iter().next().expect("a byte");
            let name = header_byte_name(*cut, FrameAddr { slot, offset });
            for (defined, term) in &mut definitions {
                if *defined == name {
                    *term = term.clone().bvxor(E::bv_const(1, 8));
                }
            }
        }
        definitions
    }

    /// The defined names.
    pub(super) fn names(&self) -> HashSet<String> {
        self.by_cut
            .iter()
            .flat_map(|(cut, defined)| defined.named(*cut).into_iter().map(|(name, _)| name))
            .collect()
    }

    /// Cut point `cut`'s defined inputs, if any.
    pub(super) fn of(&self, cut: Block) -> Option<&CutDefined> {
        self.by_cut.get(&cut)
    }

    /// How many bytes and how many value items are defined.
    pub(super) fn counts(&self) -> (usize, usize) {
        self.by_cut
            .values()
            .fold((0, 0), |(bytes, items), defined| {
                (bytes + defined.bytes.len(), items + defined.items.len())
            })
    }
}

/// OD-233: what a statement in parts defines: how many cut-input bytes and
/// value items ([`CutDefinitions::counts`]) and, for tests, where each
/// definition was claimed.
#[derive(Debug, Clone, Default)]
pub(super) struct DefinedInputs {
    pub(super) counts: (usize, usize),
    #[cfg(test)]
    pub(super) record: DefinitionRecord,
}

/// Tests only (OD-233): every stated edge into a cut point of a statement in
/// parts, as `(region, from, cut)` (`build_theorem`'s list, which its check
/// K2 reads), and each definition claim considered on one, as `(region,
/// from, cut, name, the claim)`, the claim `None` where the edge's source
/// term is the name itself (it states nothing).
#[cfg(test)]
#[derive(Debug, Clone, Default)]
pub(super) struct DefinitionRecord {
    pub(super) stated_edges: Vec<(usize, Block, Block)>,
    pub(super) claims: Vec<(usize, Block, Block, String, Option<E>)>,
}

/// Tests only (`od233-forge-item`, `od233-forge-byte`): the choice with the
/// first defined item's (byte's) term off by one at its width, in the CHOICE
/// itself, so the statement's definition, check K1 and the claims all see
/// it (a wrong choice, which its edge's claim of the edge's own source term
/// refutes; a claim that stated the chosen term instead would not). The
/// choice unchanged otherwise.
fn forged_choice(mut chosen: CutDefinitions) -> CutDefinitions {
    let (item, byte) = (mutated("od233-forge-item"), mutated("od233-forge-byte"));
    if item
        && let Some(term) = chosen
            .by_cut
            .values_mut()
            .find_map(|defined| defined.items.values_mut().next())
    {
        let width = term.bv_width();
        *term = term.clone().bvxor(E::bv_const(1, width));
    }
    if byte
        && let Some(term) = chosen
            .by_cut
            .values_mut()
            .find_map(|defined| defined.bytes.values_mut().next())
    {
        *term = term.clone().bvxor(E::bv_const(1, 8));
    }
    chosen
}

/// OD-233: one edge's source terms of its cut point's candidate inputs, for
/// the choice ([`cut_definitions`]) alone: computed as OD-182's relation
/// computes them on the edge ([`split_relation`]), bytes one by one. The
/// claims take the relation's own terms, not these.
#[derive(Debug, Clone, Default)]
pub(super) struct EdgeSources {
    pub(super) items: std::collections::BTreeMap<usize, E>,
    pub(super) bytes: std::collections::BTreeMap<(u32, i64), E>,
}

/// OD-233: the source terms on `edge` into `cut`, from the values of the
/// edge's block at its end (`values`), of each candidate input: each value
/// item that is neither `I128` (two half names) nor tainted (slice 7), its
/// term the value's on the edge (for a parameter of the cut, its edge
/// copy's) at its carrier's width; and each byte item no edge taints, its
/// term the source's byte on the edge ([`source_slot_byte`]). An input
/// without such a term is left out (it stays free).
pub(super) fn edge_sources(
    cut: &CutInterface,
    edge: &CutEdge,
    values: &HashMap<Value, E>,
    walks: &BodyWalks,
) -> EdgeSources {
    let mut sources = EdgeSources::default();
    // Tests only (`od233-taint`): a tainted input is a candidate too (a
    // measurement of whether the exclusion is reached; no control).
    let taint = !mutated("od233-taint");
    for (i, (value, carrier)) in cut.items.iter().enumerate() {
        if *carrier == Carrier::I128 || (taint && cut.tainted.contains(&value.0)) {
            continue;
        }
        let on_edge = if i < cut.params {
            edge.values[i]
        } else {
            *value
        };
        if let Some(term) = values.get(&on_edge)
            && term.bv_width() == carrier.bits()
        {
            sources.items.insert(i, term.clone());
        }
    }
    let value = |v: &Value| values[v].clone();
    for (&(slot, offset), entry) in &cut.bytes {
        let candidate = match entry {
            ByteEntry::Input { tainted, .. } => !taint || !tainted,
            ByteEntry::Closed(_) => false,
        };
        if !candidate {
            continue;
        }
        let byte = edge.state.slot_bytes[slot as usize][offset as usize];
        if let Some(SlotByte::Stored(stored)) = &byte
            && !values.contains_key(&stored.value)
        {
            continue;
        }
        sources.bytes.insert(
            (slot, offset),
            source_slot_byte(FrameAddr { slot, offset }, &byte, &value, walks),
        );
    }
    sources
}

/// OD-233: one stated edge into a cut point, for [`cut_definitions`]: the
/// region of the edge's block, the cut point and the edge's source terms
/// ([`edge_sources`]).
pub(super) struct StatedEdge {
    pub(super) region: usize,
    pub(super) cut: Block,
    pub(super) sources: EdgeSources,
}

/// OD-233: `term` with every name the statement or a chosen cut input
/// defines (`defs`) replaced by its term, when the result names only inputs
/// fixed for the run and no slot address and has at most
/// [`MAX_CLOSED_TERM_NODES`] nodes ([`run_fixed_term`]); then OD-182's bit
/// identities and OD-188's exact fold. `None` otherwise.
fn resolved_source_term(
    term: &E,
    defs: &HashMap<&str, &E>,
    memo: &mut HashMap<String, Option<E>>,
) -> Option<E> {
    // Tests only: every name the statement does not define is taken as
    // fixed (K1 then refuses the choice).
    let fixed: HashSet<String> = if mutated("od233-any-name") {
        let mut undefined = HashSet::new();
        let mut stack = vec![term];
        let mut seen = HashSet::new();
        while let Some(expr) = stack.pop() {
            for var in expr.free_vars() {
                match defs.get(var.as_str()) {
                    Some(&def) if seen.insert(var.clone()) => stack.push(def),
                    Some(_) => {}
                    None => {
                        undefined.insert(var);
                    }
                }
            }
        }
        undefined
    } else {
        HashSet::new()
    };
    let resolved = run_fixed_term(term, defs, &fixed, memo)?;
    if resolved
        .free_vars()
        .iter()
        .any(|name| parse_slot_address_name(name).is_some())
    {
        return None;
    }
    Some(folded(&bit_normalized(&resolved)))
}

/// Whether `term` resolves to the chosen `defined` ([`resolved_source_term`]).
fn resolves_to(
    term: &E,
    defined: &E,
    defs: &HashMap<&str, &E>,
    memo: &mut HashMap<String, Option<E>>,
) -> bool {
    resolved_source_term(term, defs, memo).as_ref() == Some(defined)
}

/// A cut input removed while shrinking the definition choice: item or byte.
type DroppedCutInput = (Block, Option<usize>, Option<(u32, i64)>);

/// OD-233: the cut inputs the statement defines (design §2.2). The choice is
/// untrusted: it reads only the theorem's own source terms (`edges`) and
/// definitions so far (`definitions`), never the machine, and a wrong choice
/// is refuted by the claim on its edge or refused by the checks in
/// `build_theorem`.
///
/// Seed: cut points in ascending region order; an input whose term resolves
/// to one `T` on every FORWARD edge into its cut (from an earlier region),
/// with the statement's definitions and the earlier cuts' seeds inlined, is
/// seeded with `T`. Shrink: until nothing changes, an input whose term on
/// SOME edge into its cut (a back edge included) does not resolve to its `T`
/// under the current seeds is dropped. The result is the greatest set
/// consistent on every edge, forward and back, that the seeds contain.
pub(super) fn cut_definitions(
    cuts: &std::collections::BTreeMap<Block, CutInterface>,
    edges: &[StatedEdge],
    definitions: &[(String, E)],
) -> CutDefinitions {
    if mutated("od233-off") {
        return CutDefinitions::default();
    }
    let first_edge = mutated("od233-first-edge");
    let mut chosen = CutDefinitions::default();
    let mut order: Vec<&CutInterface> = cuts.values().collect();
    order.sort_by_key(|cut| (cut.region, cut.block));
    for cut in order {
        let forward: Vec<&StatedEdge> = edges
            .iter()
            .filter(|edge| edge.cut == cut.block && edge.region < cut.region)
            .collect();
        let Some((first, rest)) = forward.split_first() else {
            continue;
        };
        let rest = if first_edge { &[][..] } else { rest };
        let seeds = chosen.definitions();
        let defs: HashMap<&str, &E> = definitions
            .iter()
            .chain(&seeds)
            .map(|(name, expr)| (name.as_str(), expr))
            .collect();
        let mut memo = HashMap::new();
        let mut seed = CutDefined::default();
        for (i, term) in &first.sources.items {
            if let Some(defined) = resolved_source_term(term, &defs, &mut memo)
                && rest.iter().all(|edge| {
                    edge.sources
                        .items
                        .get(i)
                        .is_some_and(|term| resolves_to(term, &defined, &defs, &mut memo))
                })
            {
                seed.items.insert(*i, defined);
            }
        }
        for (key, term) in &first.sources.bytes {
            if let Some(defined) = resolved_source_term(term, &defs, &mut memo)
                && rest.iter().all(|edge| {
                    edge.sources
                        .bytes
                        .get(key)
                        .is_some_and(|term| resolves_to(term, &defined, &defs, &mut memo))
                })
            {
                seed.bytes.insert(*key, defined);
            }
        }
        if !seed.is_empty() {
            chosen.by_cut.insert(cut.block, seed);
        }
    }
    if first_edge || mutated("od233-no-shrink") {
        return forged_choice(chosen);
    }
    loop {
        let seeds = chosen.definitions();
        let defs: HashMap<&str, &E> = definitions
            .iter()
            .chain(&seeds)
            .map(|(name, expr)| (name.as_str(), expr))
            .collect();
        let mut memo = HashMap::new();
        let mut dropped: Vec<DroppedCutInput> = Vec::new();
        for (cut, defined) in &chosen.by_cut {
            let into: Vec<&StatedEdge> = edges.iter().filter(|edge| edge.cut == *cut).collect();
            for (i, term) in &defined.items {
                if !into.iter().all(|edge| {
                    edge.sources
                        .items
                        .get(i)
                        .is_some_and(|on_edge| resolves_to(on_edge, term, &defs, &mut memo))
                }) {
                    dropped.push((*cut, Some(*i), None));
                }
            }
            for (key, term) in &defined.bytes {
                if !into.iter().all(|edge| {
                    edge.sources
                        .bytes
                        .get(key)
                        .is_some_and(|on_edge| resolves_to(on_edge, term, &defs, &mut memo))
                }) {
                    dropped.push((*cut, None, Some(*key)));
                }
            }
        }
        if dropped.is_empty() {
            return forged_choice(chosen);
        }
        for (cut, item, byte) in dropped {
            let defined = chosen.by_cut.get_mut(&cut).expect("a chosen cut");
            if let Some(i) = item {
                defined.items.remove(&i);
            }
            if let Some(key) = byte {
                defined.bytes.remove(&key);
            }
            if defined.is_empty() {
                chosen.by_cut.remove(&cut);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Parts
// ---------------------------------------------------------------------------

/// `definitions` and `claims` value-numbered (slice 16's part spelling): in
/// order, a definition whose right-hand side (its names already replaced,
/// [`bit_normalized`]) is a variable or a constant is that term, and one
/// whose right-hand side is the same term as an earlier kept definition's is
/// that earlier name; each is replaced everywhere after it and in the
/// claims. A replaced name equals its
/// replacement on every input that satisfies the definitions, so the claims
/// mean what they meant. The machine's and the source's spellings of one
/// computation (`p0 := e_rdi`, `m7 := (bvadd m3 k)` beside `s5 := (bvadd s2
/// k)` with `m3` and `s2` one value) become one name, and their equations
/// identities.
pub(super) fn unify_definitions(definitions: Vec<(String, E)>, claims: E) -> (Vec<(String, E)>, E) {
    let substitute = |expr: &E, env: &HashMap<String, E>| -> E {
        expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
            Ok(match node {
                E::Var { name, .. } => env.get(name).cloned(),
                _ => None,
            })
        })
        .unwrap_or_else(|never| match never {})
        .unwrap_or_else(|| expr.clone())
    };
    let mut env: HashMap<String, E> = HashMap::new();
    let mut numbered: HashMap<String, String> = HashMap::new();
    let mut kept = Vec::with_capacity(definitions.len());
    for (name, expr) in definitions {
        let expr = bit_normalized(&substitute(&expr, &env));
        if matches!(expr, E::Var { .. } | E::BvConst { .. }) {
            env.insert(name, expr);
            continue;
        }
        let key = expr.to_string();
        if let Some(earlier) = numbered.get(&key) {
            env.insert(name, E::var(earlier.clone(), expr.bv_width()));
            continue;
        }
        numbered.insert(key, name.clone());
        kept.push((name, expr));
    }
    let claims = bit_normalized(&substitute(&claims, &env));
    (kept, claims)
}

/// The most nodes a right-hand side [`substitute_bit_moves`] substitutes may
/// have (a bound on how much a repeated use can grow the formula).
const MAX_BIT_MOVE_NODES: usize = 16;

/// `definitions` and `claims` with every definition whose right-hand side
/// (its earlier substitutions made, [`bit_normalized`]) only moves bits of
/// variables and constants, an extract, a zero extension or a concatenation
/// of them of at most [`MAX_BIT_MOVE_NODES`] nodes, replaced by that term
/// everywhere after it and in the claims (slice 17's spelling, before
/// [`unify_definitions`]). A replaced name equals its term on every input
/// that satisfies the definitions, so the claims mean what they meant; once
/// the source's `p1 := x[31:0]` and the machine's `m0 := zext(x[31:0])` are
/// terms, the two sides' bytes of one stored value are one spelling.
pub(super) fn substitute_bit_moves(
    definitions: Vec<(String, E)>,
    claims: E,
) -> (Vec<(String, E)>, E) {
    let substitute = |expr: &E, env: &HashMap<String, E>| -> E {
        expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
            Ok(match node {
                E::Var { name, .. } => env.get(name).cloned(),
                _ => None,
            })
        })
        .unwrap_or_else(|never| match never {})
        .unwrap_or_else(|| expr.clone())
    };
    let mut env: HashMap<String, E> = HashMap::new();
    let mut kept = Vec::with_capacity(definitions.len());
    for (name, expr) in definitions {
        let expr = bit_moves_normalized(&substitute(&expr, &env));
        let mut budget = MAX_BIT_MOVE_NODES;
        if moves_bits(&expr, &mut budget) {
            env.insert(name, expr);
            continue;
        }
        kept.push((name, expr));
    }
    let claims = bit_moves_normalized(&substitute(&claims, &env));
    (kept, claims)
}

/// Whether `expr` only moves bits of variables and constants (an extract, a
/// zero extension or a concatenation of them) in at most `budget` nodes.
fn moves_bits(expr: &E, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match expr {
        E::Var { .. } | E::BvConst { .. } => true,
        E::Extract { operand, .. } | E::ZeroExtend { operand, .. } => moves_bits(operand, budget),
        E::Concat { hi, lo, .. } => moves_bits(hi, budget) && moves_bits(lo, budget),
        _ => false,
    }
}

/// [`bit_normalized`] after three more exact identities, applied to a
/// fixpoint (at most eight rounds), for the terms [`substitute_bit_moves`]
/// writes: `zero_extend(x)[h:l]` with `h` below `x`'s width is `x[h:l]`;
/// `x[h2:l2][h:l]` is `x[h + l2:l + l2]`; and an extract of a constant is
/// the constant of those bits. Each holds on every input. (A substituted
/// narrow index otherwise reaches every test of a 256-arm low-bit select as
/// `zero_extend(x[7:0])[j:j]`, a query AY build 12713 proves but cannot
/// render the proof of.)
pub(super) fn bit_moves_normalized(expr: &E) -> E {
    let mut current = expr.clone();
    for _ in 0..8 {
        let next = current
            .try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
                let E::Extract {
                    high, low, operand, ..
                } = node
                else {
                    return Ok(None);
                };
                let (high, low) = (*high, *low);
                Ok(match operand.as_ref() {
                    E::BvConst { value, .. } => {
                        let width = high - low + 1;
                        let bits = if width >= 64 {
                            *value >> low
                        } else {
                            (*value >> low) & ((1u64 << width) - 1)
                        };
                        Some(E::bv_const(bits, width))
                    }
                    E::ZeroExtend { operand: inner, .. } if high < inner.bv_width() => {
                        Some(inner.as_ref().clone().extract(high, low))
                    }
                    E::Extract {
                        low: inner_low,
                        operand: inner,
                        ..
                    } => Some(
                        inner
                            .as_ref()
                            .clone()
                            .extract(high + inner_low, low + inner_low),
                    ),
                    _ => None,
                })
            })
            .unwrap_or_else(|never| match never {});
        match next {
            Some(next) => current = next,
            None => break,
        }
    }
    bit_normalized(&current)
}

/// `expr` with three bit-vector identities applied bottom-up (slice 16's part
/// spelling): `concat(x[h1:l1], x[h2:l2])` with `l1 = h2 + 1` is `x[h1:l2]`;
/// `x[w-1:0]` of a `w`-bit `x` is `x`; and `zero_extend(x)[w-1:0]` of a
/// `w`-bit `x` is `x`. Each holds on every input, so the result means what
/// `expr` means. (The machine reassembles a register's bytes as a
/// concatenation of its byte extracts; the source names the register.)
pub(super) fn bit_normalized(expr: &E) -> E {
    let whole = |operand: &E, high: u32, low: u32| -> E {
        if low == 0 && high + 1 == operand.bv_width() {
            operand.clone()
        } else {
            operand.clone().extract(high, low)
        }
    };
    expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
        Ok(match node {
            E::Concat { hi, lo, .. } => match (hi.as_ref(), lo.as_ref()) {
                (
                    E::Extract {
                        high: h1,
                        low: l1,
                        operand: a,
                        ..
                    },
                    E::Extract {
                        high: h2,
                        low: l2,
                        operand: b,
                        ..
                    },
                ) if *l1 == *h2 + 1 && (std::sync::Arc::ptr_eq(a, b) || a == b) => {
                    Some(whole(a.as_ref(), *h1, *l2))
                }
                _ => None,
            },
            E::Extract {
                high,
                low: 0,
                operand,
                ..
            } => match operand.as_ref() {
                E::ZeroExtend { operand: inner, .. } if *high + 1 == inner.bv_width() => {
                    Some(inner.as_ref().clone())
                }
                _ if *high + 1 == operand.bv_width() => Some(operand.as_ref().clone()),
                _ => None,
            },
            _ => None,
        })
    })
    .unwrap_or_else(|never| match never {})
    .unwrap_or_else(|| expr.clone())
}

// ---------------------------------------------------------------------------
// Slice 18 (OD-188): constant folding and the `bvsub`-zero identity
// ---------------------------------------------------------------------------

/// The most bottom-up rounds [`folded`] rewrites a term.
const MAX_FOLD_ROUNDS: usize = 16;

/// A constant operand of [`fold_constant`]: a bit-vector's bits and width,
/// or a Boolean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Constant {
    Bits(u128, u32),
    Bool(bool),
}

/// The low `width` bits of `value` (`width` 1 to 128).
fn low_bits(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}

/// `value` as a `width`-bit two's complement number.
fn as_signed(value: u128, width: u32) -> i128 {
    let shift = 128 - width;
    ((value << shift) as i128) >> shift
}

/// A constant's value, when `expr` is one.
fn constant(expr: &E) -> Option<Constant> {
    match expr {
        E::BvConst { value, width } => Some(Constant::Bits(u128::from(*value), *width)),
        E::BoolConst(value) => Some(Constant::Bool(*value)),
        _ => None,
    }
}

/// The term of a `width`-bit value, when a [`E::BvConst`] holds it (its
/// value in 64 bits).
fn bits_term(value: u128, width: u32) -> Option<E> {
    let value = low_bits(value, width);
    u64::try_from(value)
        .ok()
        .map(|value| E::bv_const(value, width))
}

/// `node` evaluated, when every operand is a constant and the operator is
/// one SMT-LIB defines on constants exactly as written here (a division or
/// remainder by zero as SMT-LIB defines it: `bvudiv` all ones, `bvurem` the
/// dividend, `bvsdiv` through `bvudiv` of the magnitudes); `None` otherwise,
/// or when the value is a bit-vector no [`E::BvConst`] holds (wider than 64
/// bits with a bit above the 64th set). An `ite` is never folded here, nor
/// a Boolean connective; an equation of two equal constants neither (only
/// two distinct ones, to `false`).
pub(super) fn fold_constant(node: &E) -> Option<E> {
    let bits = |expr: &E| match constant(expr)? {
        Constant::Bits(value, width) => Some((value, width)),
        Constant::Bool(_) => None,
    };
    let pair = |lhs: &E, rhs: &E| Some((bits(lhs)?.0, bits(rhs)?.0));
    let udiv = |a: u128, b: u128, width: u32| {
        a.checked_div(b)
            .unwrap_or_else(|| low_bits(u128::MAX, width))
    };
    let value = match node {
        E::BvAdd { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a.wrapping_add(b), *width)
        }
        E::BvSub { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a.wrapping_sub(b), *width)
        }
        E::BvMul { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a.wrapping_mul(b), *width)
        }
        E::BvAnd { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a & b, *width)
        }
        E::BvOr { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a | b, *width)
        }
        E::BvXor { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (a ^ b, *width)
        }
        E::BvNeg { operand, width } => (bits(operand)?.0.wrapping_neg(), *width),
        E::BvShl { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (if b >= u128::from(*width) { 0 } else { a << b }, *width)
        }
        E::BvLshr { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (if b >= u128::from(*width) { 0 } else { a >> b }, *width)
        }
        E::BvAshr { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            let shift = b.min(u128::from(*width - 1)) as u32;
            ((as_signed(a, *width) >> shift) as u128, *width)
        }
        E::BvUDiv { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (udiv(a, b, *width), *width)
        }
        E::BvURem { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            (if b == 0 { a } else { a % b }, *width)
        }
        E::BvSDiv { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            let width = *width;
            let negative = |v: u128| (v >> (width - 1)) & 1 == 1;
            let neg = |v: u128| low_bits(v.wrapping_neg(), width);
            let quotient = match (negative(a), negative(b)) {
                (false, false) => udiv(a, b, width),
                (true, false) => neg(udiv(neg(a), b, width)),
                (false, true) => neg(udiv(a, neg(b), width)),
                (true, true) => udiv(neg(a), neg(b), width),
            };
            (quotient, width)
        }
        E::Concat { hi, lo, width } => {
            let ((h, _), (l, low_width)) = (bits(hi)?, bits(lo)?);
            ((h << low_width) | l, *width)
        }
        E::ZeroExtend { operand, width, .. } => (bits(operand)?.0, *width),
        E::SignExtend {
            operand,
            extra_bits,
            width,
        } => (
            as_signed(bits(operand)?.0, *width - *extra_bits) as u128,
            *width,
        ),
        E::Extract {
            high, low, operand, ..
        } => (bits(operand)?.0 >> low, high - low + 1),
        E::BvUlt { lhs, rhs, .. } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(a < b));
        }
        E::BvUle { lhs, rhs, .. } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(a <= b));
        }
        E::BvUgt { lhs, rhs, .. } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(a > b));
        }
        E::BvUge { lhs, rhs, .. } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(a >= b));
        }
        E::BvSlt { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(as_signed(a, *width) < as_signed(b, *width)));
        }
        E::BvSle { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(as_signed(a, *width) <= as_signed(b, *width)));
        }
        E::BvSgt { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(as_signed(a, *width) > as_signed(b, *width)));
        }
        E::BvSge { lhs, rhs, width } => {
            let (a, b) = pair(lhs, rhs)?;
            return Some(E::bool_const(as_signed(a, *width) >= as_signed(b, *width)));
        }
        E::Eq { lhs, rhs } => {
            let (a, b) = (constant(lhs)?, constant(rhs)?);
            return (a != b).then(|| E::bool_const(false));
        }
        _ => return None,
    };
    bits_term(value.0, value.1)
}

/// One bottom-up step of [`folded`] on `node` (its operands already
/// rewritten): an extract identity, a fold, the `bvsub`-zero identity, or
/// a division or remainder by a constant power of two as its shift or mask.
fn fold_step(node: &E) -> Option<E> {
    match node {
        E::Extract {
            high, low, operand, ..
        } => {
            let (high, low) = (*high, *low);
            if low == 0 && high + 1 == operand.bv_width() {
                return Some(operand.as_ref().clone());
            }
            match operand.as_ref() {
                E::BvConst { .. } => fold_constant(node),
                E::Extract {
                    low: inner_low,
                    operand: inner,
                    ..
                } => Some(
                    inner
                        .as_ref()
                        .clone()
                        .extract(high + inner_low, low + inner_low),
                ),
                E::ZeroExtend { operand: inner, .. } if high < inner.bv_width() => {
                    Some(inner.as_ref().clone().extract(high, low))
                }
                _ => None,
            }
        }
        E::Concat { hi, lo, .. } => match (hi.as_ref(), lo.as_ref()) {
            (
                E::Extract {
                    high: h1,
                    low: l1,
                    operand: a,
                    ..
                },
                E::Extract {
                    high: h2,
                    low: l2,
                    operand: b,
                    ..
                },
            ) if *l1 == *h2 + 1 && (std::sync::Arc::ptr_eq(a, b) || a == b) => {
                if *l2 == 0 && *h1 + 1 == a.bv_width() {
                    Some(a.as_ref().clone())
                } else {
                    Some(a.as_ref().clone().extract(*h1, *l2))
                }
            }
            _ => fold_constant(node),
        },
        E::Eq { lhs, rhs } => {
            if lhs == rhs {
                return None;
            }
            if let Some(folded) = fold_constant(node) {
                return Some(folded);
            }
            // `(= (bvsub x y) 0)`, either way round, is `(= x y)`: `x - y`
            // is zero exactly when `x` is `y`, at one width.
            for (difference, zero) in [(lhs, rhs), (rhs, lhs)] {
                if let (E::BvSub { lhs: x, rhs: y, .. }, E::BvConst { value: 0, .. }) =
                    (difference.as_ref(), zero.as_ref())
                {
                    return Some(if x == y {
                        E::bool_const(true)
                    } else {
                        x.as_ref().clone().eq_expr(y.as_ref().clone())
                    });
                }
            }
            None
        }
        // `bvudiv x 2^k` is `bvlshr x k` (`x` for `k = 0`) and `bvurem x 2^k`
        // is `bvand x (2^k - 1)` (`0` for `k = 0`), for every `x` at one
        // width: the divisor is not zero. A substituted definition can make
        // constant a divisor that its own block did not (OD-233's defined
        // cut inputs), and a solver bit-blasts the division circuit left
        // behind: AY build 13556 takes 50 s on one 64-bit
        // `(bvudiv s (_ bv1 64))` that it decides in 0.2 s spelled `s` (the
        // 2026-11-07 G-SEFRT measurement).
        E::BvUDiv { lhs, rhs, width } | E::BvURem { lhs, rhs, width } => fold_constant(node)
            .or_else(|| {
                let Some(Constant::Bits(divisor, _)) = constant(rhs) else {
                    return None;
                };
                let divisor = low_bits(divisor, *width);
                if !divisor.is_power_of_two() {
                    return None;
                }
                let k = divisor.trailing_zeros();
                let x = lhs.as_ref().clone();
                if matches!(node, E::BvUDiv { .. }) {
                    if k == 0 {
                        Some(x)
                    } else {
                        Some(x.bvlshr(bits_term(u128::from(k), *width)?))
                    }
                } else if k == 0 {
                    bits_term(0, *width)
                } else {
                    Some(x.bvand(bits_term(divisor - 1, *width)?))
                }
            }),
        E::Ite { .. } | E::Not { .. } | E::And { .. } | E::Or { .. } => None,
        _ => fold_constant(node),
    }
}

/// `expr` with [`fold_step`]'s exact rewrites applied bottom-up to a
/// fixpoint (at most [`MAX_FOLD_ROUNDS`] rounds): the extract identities of
/// [`bit_moves_normalized`] and [`bit_normalized`]; every operator whose
/// operands are all constants replaced by its value ([`fold_constant`]);
/// `(= (bvsub x y) 0)` by `(= x y)`; and an unsigned division or remainder
/// by a constant power of two by its shift or mask. Each rewrite holds on
/// every input, so the result means what `expr` means. (Behind a definition
/// name, AY build 12713 multiplies a sign-extended constant out as a
/// variable, and its proof of a `bvsub` compared with zero takes Clean past
/// its budget; the slice-18 report measures both. AY build 13556 bit-blasts
/// a division by a constant power of two as a division circuit.)
pub(super) fn folded(expr: &E) -> E {
    let mut current = expr.clone();
    for _ in 0..MAX_FOLD_ROUNDS {
        let next = current
            .try_rewrite_dag::<std::convert::Infallible>(&mut |node| Ok(fold_step(node)))
            .unwrap_or_else(|never| match never {});
        match next {
            Some(next) if next != current => current = next,
            _ => break,
        }
    }
    current
}

/// The right-nested conjunction of `claims` after [`folded`], keeping the
/// shape the structural check reads (a conjunction of items, each an
/// equation, a Boolean literal or a guarded `(or (not G) X)`): an equation's
/// two sides are folded and an equation of one term with itself dropped;
/// another item is folded and split into its conjuncts, each `true` one
/// dropped; a guard literal folded to `true` is dropped from its guard, an
/// item whose guard has a literal folded to `false` holds and is dropped, and
/// an item whose guard is left empty is its conjuncts. Equivalent to
/// `claims`. `None` when no claim is left.
pub(super) fn folded_claims(claims: &E) -> Option<E> {
    fn conjuncts(mut expr: &E) -> Vec<&E> {
        let mut terms = Vec::new();
        while let E::And { lhs, rhs } = expr {
            terms.push(lhs.as_ref());
            expr = rhs.as_ref();
        }
        terms.push(expr);
        terms
    }
    fn conjunction(terms: Vec<E>) -> Option<E> {
        terms
            .into_iter()
            .rev()
            .reduce(|tail, term| term.and_expr(tail))
    }
    let item = |claim: &E| -> Vec<E> {
        match claim {
            E::Eq { lhs, rhs } if lhs.try_bv_width().is_ok() => {
                let (lhs, rhs) = (folded(lhs), folded(rhs));
                if lhs == rhs {
                    Vec::new()
                } else {
                    vec![lhs.eq_expr(rhs)]
                }
            }
            other => {
                let folded = folded(other);
                conjuncts(&folded)
                    .into_iter()
                    .filter(|term| **term != E::bool_const(true))
                    .cloned()
                    .collect()
            }
        }
    };
    let mut items: Vec<E> = Vec::new();
    for claim in conjuncts(claims) {
        match claim {
            E::Or { lhs, rhs } if matches!(lhs.as_ref(), E::Not { .. }) => {
                let E::Not { operand: guard } = lhs.as_ref() else {
                    unreachable!("a guard")
                };
                let literals: Vec<E> = conjuncts(guard).into_iter().map(folded).collect();
                if literals.contains(&E::bool_const(false)) {
                    continue;
                }
                let literals: Vec<E> = literals
                    .into_iter()
                    .filter(|literal| *literal != E::bool_const(true))
                    .collect();
                let body: Vec<E> = conjuncts(rhs).into_iter().flat_map(item).collect();
                let Some(body) = conjunction(body) else {
                    continue;
                };
                match conjunction(literals) {
                    Some(guard) => items.push(guard.not_expr().or_expr(body)),
                    None => items.extend(conjuncts(&body).into_iter().cloned()),
                }
            }
            other => items.extend(item(other)),
        }
    }
    conjunction(items)
}

/// The most rounds [`folded_spelling`] inlines and folds the claims.
const MAX_FOLD_SPELLING_ROUNDS: usize = 64;

/// Slice 18's first spelling (OD-188): slice 17's spelling with every
/// right-hand side [`folded`] ([`fold_step`]'s extract identities, constant
/// folding and the `bvsub`-zero identity) and the claims [`folded_claims`]
/// after each round of inlining:
///
/// 1. in definition order, a definition whose folded right-hand side (its
///    earlier substitutions made) only moves bits of variables and constants
///    (at most [`MAX_BIT_MOVE_NODES`] nodes, a constant included) is that term
///    ([`substitute_bit_moves`]);
/// 2. in order, a definition whose folded right-hand side is a variable or a
///    constant is that term, and one whose folded right-hand side is an
///    earlier kept definition's is that name ([`unify_definitions`]);
/// 3. every definition used at most once is inlined ([`inline_single_use`]),
///    then, to a fixpoint (at most [`MAX_FOLD_SPELLING_ROUNDS`] rounds), the
///    claims are folded, every identity is dropped ([`drop_identities`]) and
///    the definitions only those used are inlined.
///
/// Each step is exact under the definitions (slice 16's meta-argument, the
/// rewrites holding on every input), so the result is equivalent to the
/// theorem. `None` when no claim is left.
pub(super) fn folded_spelling(
    definitions: Vec<(String, E)>,
    claims: E,
) -> Option<(Vec<(String, E)>, E)> {
    let substitute = |expr: &E, env: &HashMap<String, E>| -> E {
        expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
            Ok(match node {
                E::Var { name, .. } => env.get(name).cloned(),
                _ => None,
            })
        })
        .unwrap_or_else(|never| match never {})
        .unwrap_or_else(|| expr.clone())
    };
    let mut env: HashMap<String, E> = HashMap::new();
    let mut moved = Vec::with_capacity(definitions.len());
    for (name, expr) in definitions {
        let expr = folded(&substitute(&expr, &env));
        let mut budget = MAX_BIT_MOVE_NODES;
        if moves_bits(&expr, &mut budget) {
            env.insert(name, expr);
            continue;
        }
        moved.push((name, expr));
    }
    let claims = substitute(&claims, &env);
    let mut env: HashMap<String, E> = HashMap::new();
    let mut numbered: HashMap<String, String> = HashMap::new();
    let mut kept = Vec::with_capacity(moved.len());
    for (name, expr) in moved {
        let expr = folded(&substitute(&expr, &env));
        if matches!(expr, E::Var { .. } | E::BvConst { .. }) {
            env.insert(name, expr);
            continue;
        }
        let key = expr.to_string();
        if let Some(earlier) = numbered.get(&key) {
            env.insert(name, E::var(earlier.clone(), expr.bv_width()));
            continue;
        }
        numbered.insert(key, name.clone());
        kept.push((name, expr));
    }
    let claims = folded_claims(&substitute(&claims, &env))?;
    let (mut kept, _, mut stated) = inline_single_use(kept, E::bool_const(true), claims);
    for _ in 0..MAX_FOLD_SPELLING_ROUNDS {
        stated = folded_claims(&stated)?;
        let (claims, dropped) = drop_identities(&stated)?;
        let (next, _, next_claims) = inline_single_use(kept.clone(), E::bool_const(true), claims);
        if !dropped && next == kept && next_claims == stated {
            break;
        }
        kept = next;
        stated = next_claims;
    }
    Some((kept, stated))
}

/// One part of `statement`: `(= true claims)` under the definitions `kept`
/// (in order), declaring the free inputs of `free` (the statement's, in its
/// order) it reads, then its definitions; named, categorized and attributed
/// as the statement.
pub(super) fn part_obligation(
    statement: &ProofObligation,
    free: &[(String, u32)],
    kept: Vec<(String, E)>,
    claims: E,
) -> ProofObligation {
    let used: HashSet<String> = kept
        .iter()
        .flat_map(|(_, expr)| expr.free_vars())
        .chain(claims.free_vars())
        .collect();
    let inputs: Vec<(String, u32)> = free
        .iter()
        .filter(|(name, _)| used.contains(name))
        .cloned()
        .chain(
            kept.iter()
                .map(|(name, expr)| (name.clone(), expr.bv_width())),
        )
        .collect();
    ProofObligation {
        name: statement.name.clone(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: claims,
        inputs,
        preconditions: kept
            .into_iter()
            .rev()
            .map(|(name, expr)| {
                let width = expr.bv_width();
                E::var(name, width).eq_expr(expr)
            })
            .collect(),
        fp_inputs: Vec::new(),
        category: statement.category,
        machine_side_provenance: statement.machine_side_provenance.clone(),
    }
}

/// A part's second spelling (slice 18, OD-189): `definitions` and `claims`,
/// already spelled as slice 16 spells a part, with every definition that
/// only moves bits of variables and constants substituted
/// ([`substitute_bit_moves`]), value-numbered once more
/// ([`unify_definitions`]) and inlined ([`inline_single_use`]), every claim
/// that becomes an identity dropped, to a fixpoint: slice 17's spelling over
/// the part. Each step is exact under the definitions (slice 16's
/// meta-argument). `None` when no claim is left.
pub(super) fn respelled_part(
    definitions: Vec<(String, E)>,
    claims: E,
) -> Option<(Vec<(String, E)>, E)> {
    let (moved, claims) = substitute_bit_moves(definitions, claims);
    let (unified, claims) = unify_definitions(moved, claims);
    let (mut kept, _, mut stated) = inline_single_use(unified, E::bool_const(true), claims);
    loop {
        match drop_identities(&stated)? {
            (dropped, true) => {
                let (next, _, next_claims) = inline_single_use(kept, E::bool_const(true), dropped);
                kept = next;
                stated = next_claims;
            }
            (_, false) => return Some((kept, stated)),
        }
    }
}

/// The parts of a theorem stated in parts (slice 16): the statement's claims
/// in consecutive groups, `region_claims[r]` of them for region `r`; each
/// group is one part, `(= true (and K_1 ... K_m))`, under the cone of the
/// statement's definitions its claims reach, value-numbered
/// ([`unify_definitions`]), with every definition used at most once
/// substituted into its use and every claim those substitutions make an
/// identity dropped (slice 9's spelling; a part whose spelling fails the
/// structural check is stated without the substitutions), then (slice 18,
/// OD-189) spelled again as slice 17 spells a theorem ([`respelled_part`]:
/// the bit moves substituted, value numbering, inlining and identity
/// dropping once more; kept only when it passes the structural check). A
/// region with no claim, or whose claims all drop, is no part, unless every
/// region's claims
/// drop: a theorem is never stated by identities alone (slice 9's rule), so
/// then every region with a claim is stated without the substitutions. Each
/// part declares exactly the statement's free inputs it reads, in the
/// statement's order, and is named `<statement name> | part k of n`.
/// Mechanical: [`check_x86_body_parts`] re-derives it.
pub(crate) fn split_parts(
    statement: &ProofObligation,
    region_claims: &[usize],
) -> Result<Vec<ProofObligation>, String> {
    if statement.trust_ir_expr != E::bool_const(true) {
        return Err("a statement in parts is stated against `true`".into());
    }
    let mut definitions: Vec<(String, E)> = Vec::with_capacity(statement.preconditions.len());
    for premise in statement.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            return Err(format!("premise {premise} is not an equation"));
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            return Err(format!("premise {premise} does not define a name"));
        };
        definitions.push((name.clone(), rhs.as_ref().clone()));
    }
    let defined: HashSet<&str> = definitions.iter().map(|(name, _)| name.as_str()).collect();
    let free: Vec<(String, u32)> = statement
        .inputs
        .iter()
        .filter(|(name, _)| !defined.contains(name.as_str()))
        .cloned()
        .collect();
    // The statement's claims: the right-nested conjunction of exactly as
    // many claims as its regions account for (the last one may itself be a
    // conjunction).
    let total: usize = region_claims.iter().sum();
    if total == 0 {
        return Err("a statement in parts has no claim".into());
    }
    let mut claims: Vec<E> = Vec::with_capacity(total);
    let mut rest = &statement.aarch64_expr;
    for _ in 1..total {
        let E::And { lhs, rhs } = rest else {
            return Err(format!(
                "the statement has {} claims where its regions account for {total}",
                claims.len() + 1
            ));
        };
        claims.push(lhs.as_ref().clone());
        rest = rhs.as_ref();
    }
    claims.push(rest.clone());
    let by_name: HashMap<&str, &E> = definitions
        .iter()
        .map(|(name, expr)| (name.as_str(), expr))
        .collect();
    let conjunction = |terms: Vec<E>| {
        terms
            .into_iter()
            .rev()
            .reduce(|tail, term| term.and_expr(tail))
    };
    let part = |kept: Vec<(String, E)>, claims: E| -> ProofObligation {
        part_obligation(statement, &free, kept, claims)
    };
    let free_of = |obligation: &ProofObligation| -> Vec<(String, u32)> {
        let defined: HashSet<String> = obligation
            .preconditions
            .iter()
            .filter_map(|premise| match premise {
                E::Eq { lhs, .. } => match lhs.as_ref() {
                    E::Var { name, .. } => Some(name.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        obligation
            .inputs
            .iter()
            .filter(|(name, _)| !defined.contains(name))
            .cloned()
            .collect()
    };
    /// A region's spelling: its part, or no claim left once identities drop
    /// (its cone and claims kept for the plain statement).
    enum Spelled {
        Part(ProofObligation),
        Empty(Vec<(String, E)>, E),
    }
    let mut spelled: Vec<Spelled> = Vec::new();
    let mut at = 0;
    for count in region_claims {
        let mine: Vec<E> = claims[at..at + count].to_vec();
        at += count;
        let Some(claim) = conjunction(mine) else {
            continue;
        };
        let mut reached: HashSet<String> = HashSet::new();
        let mut pending: Vec<String> = claim.free_vars();
        while let Some(name) = pending.pop() {
            if reached.insert(name.clone())
                && let Some(expr) = by_name.get(name.as_str())
            {
                pending.extend(expr.free_vars());
            }
        }
        let cone: Vec<(String, E)> = definitions
            .iter()
            .filter(|(name, _)| reached.contains(name))
            .cloned()
            .collect();
        // Value-numbered ([`unify_definitions`]) and inlined (slice 9's
        // spelling), every claim the substitutions make an identity dropped.
        // A region whose claims all drop states nothing that needs a proof;
        // one whose spelling fails the structural check is stated plainly.
        let (unified, unified_claim) = unify_definitions(cone.clone(), claim.clone());
        let (mut kept, _, mut stated) =
            inline_single_use(unified, E::bool_const(true), unified_claim);
        let mut emptied = false;
        loop {
            match drop_identities(&stated) {
                Some((dropped, true)) => {
                    let (next, _, next_claims) =
                        inline_single_use(kept, E::bool_const(true), dropped);
                    kept = next;
                    stated = next_claims;
                }
                Some((_, false)) => break,
                None => {
                    emptied = true;
                    break;
                }
            }
        }
        if emptied {
            spelled.push(Spelled::Empty(cone, claim));
            continue;
        }
        let inlined = part(kept.clone(), stated.clone());
        let (first, first_definitions, first_claims) =
            if check_definitional_part(&inlined, &free_of(&inlined)).is_ok() {
                (inlined, kept, stated)
            } else {
                let plain = part(cone.clone(), claim.clone());
                check_definitional_part(&plain, &free_of(&plain))?;
                (plain, cone.clone(), claim.clone())
            };
        #[cfg(test)]
        if super::LEGACY_SPELLING.with(std::cell::Cell::get) {
            spelled.push(Spelled::Part(first));
            continue;
        }
        // Slice 18 (OD-189): the part so spelled is spelled again as slice
        // 17 spells a theorem ([`respelled_part`]). A part whose claims all
        // drop then is no part; one whose second spelling fails the
        // structural check keeps the first.
        let (second, second_definitions, second_claims) =
            match respelled_part(first_definitions.clone(), first_claims.clone()) {
                None => {
                    spelled.push(Spelled::Empty(cone, claim));
                    continue;
                }
                Some((kept, stated)) => {
                    let again = part(kept.clone(), stated.clone());
                    if check_definitional_part(&again, &free_of(&again)).is_ok() {
                        (again, kept, stated)
                    } else {
                        (first, first_definitions, first_claims)
                    }
                }
            };
        // Slice 19 (OD-195): then the full canonical spelling
        // ([`normal::spelled`]). A part it empties is no part; one that holds
        // a term outside its vocabulary, or whose spelling fails the part
        // check, keeps the second spelling.
        match normal::spelled(
            &second_definitions,
            &second_claims,
            normal_groups(normal::Groups::CANONICAL),
        ) {
            normal::Normal::Emptied => spelled.push(Spelled::Empty(cone, claim)),
            normal::Normal::Spelled((kept, stated)) => {
                let third = part(kept, stated);
                if check_definitional_part(&third, &free_of(&third)).is_ok() {
                    spelled.push(Spelled::Part(third));
                } else {
                    spelled.push(Spelled::Part(second));
                }
            }
            normal::Normal::Declined => spelled.push(Spelled::Part(second)),
        }
    }
    // A theorem is never stated by identities alone (slice 9's rule): when
    // every region's claims drop, every region is stated plainly.
    let mut groups: Vec<ProofObligation> = Vec::with_capacity(spelled.len());
    if spelled
        .iter()
        .all(|region| matches!(region, Spelled::Empty(..)))
    {
        for region in spelled {
            let Spelled::Empty(cone, claim) = region else {
                unreachable!("every region is empty");
            };
            let plain = part(cone, claim);
            check_definitional_part(&plain, &free_of(&plain))?;
            groups.push(plain);
        }
    } else {
        groups.extend(spelled.into_iter().filter_map(|region| match region {
            Spelled::Part(part) => Some(part),
            Spelled::Empty(..) => None,
        }));
    }
    let n = groups.len();
    for (k, group) in groups.iter_mut().enumerate() {
        group.name = format!(
            "{}{X86_BODY_PART_SEPARATOR}part {} of {n}",
            statement.name,
            k + 1
        );
    }
    Ok(groups)
}

// ---------------------------------------------------------------------------
// Slice 19 (OD-197): a theorem or part replayed claim by claim
// ---------------------------------------------------------------------------

/// The separator of a claim's name in the obligation it was cut from.
pub const X86_BODY_CLAIM_SEPARATOR: &str = " | claim ";

/// The most claims [`claim_parts`] states one by one: a theorem or part with
/// more distinct claims is not split (its replay keeps its whole verdict).
pub(super) const MAX_CLAIM_PARTS: usize = 64;

/// Slice 19 (OD-197): `obligation`, a theorem or part stated against `true`
/// whose claims are a right-nested conjunction of at least two distinct
/// claims, stated as one obligation per distinct claim, in order (a claim
/// repeated is stated once): `(= true K_i)` under the cone of the
/// obligation's definitions `K_i` reaches, in their order, declaring
/// exactly the obligation's free inputs it reads, in the obligation's order,
/// named `<obligation name> | claim i of m`. Mechanical: the conjunction of
/// the claim parts is the obligation's claims, each part's definitions are
/// some of the obligation's (each a fresh name defined once), so the
/// obligation holds exactly when every claim part does, and a model of one
/// claim part's negation extends to the obligation's (its other
/// definitions defining fresh names). Each claim part passes the part check
/// ([`check_definitional_part`]); `Err` when the obligation is not stated
/// against `true`, has fewer than two distinct claims, more than
/// [`MAX_CLAIM_PARTS`], or a claim part fails the check.
pub(crate) fn claim_parts(obligation: &ProofObligation) -> Result<Vec<ProofObligation>, String> {
    if obligation.trust_ir_expr != E::bool_const(true) {
        return Err("only a conjunctive obligation is stated claim by claim".into());
    }
    let mut definitions: Vec<(String, E)> = Vec::with_capacity(obligation.preconditions.len());
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            return Err(format!("premise {premise} is not an equation"));
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            return Err(format!("premise {premise} does not define a name"));
        };
        definitions.push((name.clone(), rhs.as_ref().clone()));
    }
    let defined: HashSet<&str> = definitions.iter().map(|(name, _)| name.as_str()).collect();
    let free: Vec<(String, u32)> = obligation
        .inputs
        .iter()
        .filter(|(name, _)| !defined.contains(name.as_str()))
        .cloned()
        .collect();
    let mut claims: Vec<&E> = Vec::new();
    let mut rest = &obligation.aarch64_expr;
    while let E::And { lhs, rhs } = rest {
        if !claims.contains(&lhs.as_ref()) {
            claims.push(lhs.as_ref());
        }
        rest = rhs.as_ref();
    }
    if !claims.contains(&rest) {
        claims.push(rest);
    }
    let m = claims.len();
    if m < 2 {
        return Err("fewer than two distinct claims".into());
    }
    if m > MAX_CLAIM_PARTS {
        return Err(format!(
            "{m} distinct claims (a claim split states at most {MAX_CLAIM_PARTS})"
        ));
    }
    let by_name: HashMap<&str, &E> = definitions
        .iter()
        .map(|(name, expr)| (name.as_str(), expr))
        .collect();
    let mut parts = Vec::with_capacity(m);
    for (k, claim) in claims.into_iter().enumerate() {
        let mut reached: HashSet<String> = HashSet::new();
        let mut pending: Vec<String> = claim.free_vars();
        while let Some(name) = pending.pop() {
            if reached.insert(name.clone())
                && let Some(expr) = by_name.get(name.as_str())
            {
                pending.extend(expr.free_vars());
            }
        }
        let cone: Vec<(String, E)> = definitions
            .iter()
            .filter(|(name, _)| reached.contains(name))
            .cloned()
            .collect();
        let mut part = part_obligation(obligation, &free, cone, claim.clone());
        part.name = format!(
            "{}{X86_BODY_CLAIM_SEPARATOR}{} of {m}",
            obligation.name,
            k + 1
        );
        let part_free: Vec<(String, u32)> = {
            let kept: HashSet<String> = part
                .preconditions
                .iter()
                .filter_map(|premise| match premise {
                    E::Eq { lhs, .. } => match lhs.as_ref() {
                        E::Var { name, .. } => Some(name.clone()),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            part.inputs
                .iter()
                .filter(|(name, _)| !kept.contains(name))
                .cloned()
                .collect()
        };
        check_definitional_part(&part, &part_free)
            .map_err(|why| format!("claim {} of {m}: {why}", k + 1))?;
        parts.push(part);
    }
    Ok(parts)
}

// ---------------------------------------------------------------------------
// Slice 23 (OD-206): an obligation replayed once more as its generalization
// ---------------------------------------------------------------------------

/// The suffix of a generalization's name, after the name of the obligation
/// it generalizes.
pub const X86_BODY_GENERALIZED_SUFFIX: &str = " | generalized";

/// Slice 23 (OD-206): whether `name` names the generalization of an x86-64
/// body theorem, part or claim ([`generalize`]).
pub fn is_x86_body_generalized_name(name: &str) -> bool {
    name.starts_with(X86_BODY_OBLIGATION_NAME) && name.ends_with(X86_BODY_GENERALIZED_SUFFIX)
}

/// Slice 23 (ruling OD-206): `obligation` (a theorem, a part or a claim)
/// generalized over its arithmetic leaves ([`normal::generalized`]: `comm`
/// and `wide`, then every product of two non-constant terms, quotient or
/// remainder by a non-constant divisor and variable shift a fresh free input
/// `ar{k}` of its width, numbered in structural first occurrence; a
/// definition that is a bare leaf substituted; the definitions no claim
/// reaches dropped), its claims that become identities dropped (slice 9's
/// rule; a one-path theorem whose two sides become one term is no
/// generalization). Declares the obligation's free inputs it reads (in its
/// order), then the leaves, then its definitions; named `<obligation name> |
/// generalized`; passes the structural check its spelling asks for.
///
/// Mechanical, so every consumer re-derives it ([`X86BodyClaims::check`]).
/// Sound by instantiation (the design's Theorem B): a model of the
/// obligation's negation, extended with each leaf at the value its node
/// computes there, is a model of the generalization's negation; so a valid
/// generalization makes the obligation valid. The converse fails (a claim may
/// need a bit of an operation), so a satisfiable generalization is no
/// counterexample (OD-200's rule). `Err` when there is no generalization:
/// no arithmetic node, every claim an identity, a term outside the
/// vocabulary, a free input already named `ar{k}`, or a failed check.
pub(crate) fn generalize(obligation: &ProofObligation) -> Result<ProofObligation, String> {
    generalize_traced(obligation).map(|(generalized, _)| generalized)
}

/// [`generalize`], with each leaf's name and the term it stands for (in leaf
/// order; tests check the instantiation with them).
pub(super) fn generalize_traced(
    obligation: &ProofObligation,
) -> Result<(ProofObligation, Vec<(String, E)>), String> {
    if !obligation.fp_inputs.is_empty() {
        return Err("floating-point inputs are outside the body theorem".into());
    }
    let mut definitions: Vec<(String, E)> = Vec::with_capacity(obligation.preconditions.len());
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            return Err(format!("premise {premise} is not an equation"));
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            return Err(format!("premise {premise} does not define a name"));
        };
        definitions.push((name.clone(), rhs.as_ref().clone()));
    }
    let defined: HashSet<&str> = definitions.iter().map(|(name, _)| name.as_str()).collect();
    let free: Vec<(String, u32)> = obligation
        .inputs
        .iter()
        .filter(|(name, _)| !defined.contains(name.as_str()))
        .cloned()
        .collect();
    if free
        .iter()
        .any(|(name, _)| normal::is_arith_leaf_name(name))
    {
        return Err("a free input is already named as an arithmetic leaf".into());
    }
    let conjunctive = obligation.trust_ir_expr == E::bool_const(true);
    let sides: Vec<E> = if conjunctive {
        vec![obligation.aarch64_expr.clone()]
    } else {
        vec![
            obligation.trust_ir_expr.clone(),
            obligation.aarch64_expr.clone(),
        ]
    };
    let general = normal::generalized(&definitions, &sides).ok_or_else(|| {
        "no arithmetic node to generalize (or a term outside the vocabulary, or a leaf name \
             already taken)"
            .to_owned()
    })?;
    let (source, machine) = if conjunctive {
        let (claims, _) = drop_identities(&general.sides[0])
            .ok_or_else(|| "every generalized claim is an identity".to_owned())?;
        (E::bool_const(true), claims)
    } else {
        let [source, machine] = general.sides.as_slice() else {
            unreachable!("two sides");
        };
        if source == machine {
            return Err("the generalized sides are one term".into());
        }
        (source.clone(), machine.clone())
    };
    let used: HashSet<String> = general
        .definitions
        .iter()
        .flat_map(|(_, expr)| expr.free_vars())
        .chain(source.free_vars())
        .chain(machine.free_vars())
        .collect();
    let declared: Vec<(String, u32)> = free
        .into_iter()
        .filter(|(name, _)| used.contains(name))
        .chain(general.leaves.iter().cloned())
        .collect();
    let generalized = ProofObligation {
        name: format!("{}{X86_BODY_GENERALIZED_SUFFIX}", obligation.name),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: declared
            .iter()
            .cloned()
            .chain(
                general
                    .definitions
                    .iter()
                    .map(|(name, expr)| (name.clone(), expr.bv_width())),
            )
            .collect(),
        preconditions: general
            .definitions
            .into_iter()
            .rev()
            .map(|(name, expr)| {
                let width = expr.bv_width();
                E::var(name, width).eq_expr(expr)
            })
            .collect(),
        fp_inputs: Vec::new(),
        category: obligation.category,
        machine_side_provenance: obligation.machine_side_provenance.clone(),
    };
    let checked = if conjunctive {
        check_definitional_part(&generalized, &declared)
    } else {
        check_definitional(&generalized, &declared)
    };
    checked.map_err(|why| format!("the generalization fails the structural check: {why}"))?;
    let nodes = general
        .leaves
        .iter()
        .map(|(name, _)| name.clone())
        .zip(general.nodes)
        .collect();
    Ok((generalized, nodes))
}

/// THE part inventory check (slice 16): `parts` are exactly the parts of
/// `statement` grouped by `region_claims` ([`split_parts`]), in order, at
/// least one, each of them structurally definitional. The owner, the
/// verifier before any credit and the proof emitter before any export each
/// run this one check, so no route credits or publishes a theorem with a part
/// missing, added, reordered or changed.
pub fn check_x86_body_parts(
    statement: &ProofObligation,
    region_claims: &[usize],
    parts: &[ProofObligation],
) -> Result<(), String> {
    if parts.is_empty() {
        return Err("a theorem stated in parts has no part".into());
    }
    let expected = split_parts(statement, region_claims)?;
    if expected.len() != parts.len() {
        return Err(format!(
            "the theorem has {} parts where its statement has {}",
            parts.len(),
            expected.len()
        ));
    }
    if let Some(k) = expected.iter().zip(parts).position(|(a, b)| a != b) {
        return Err(format!(
            "part {} of {} is not the statement's part",
            k + 1,
            parts.len()
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The owner of a function stated in parts
// ---------------------------------------------------------------------------

/// Build the theorem of a source past the single-query bounds, stated in
/// parts (slice 16; see the module documentation): plan the cut points
/// ([`plan_points`], or the test policy's), cut the blocks a point falls
/// inside ([`rewrite_pieces`]), admit the regions from their cut interfaces
/// ([`admitted_cuts`]), bound each region, walk the machine from the same
/// interfaces ([`walk_cuts`]), state the theorem with the relation on every
/// cut edge, and split it into its parts ([`split_parts`]). Every row,
/// definition and site keeps its original coordinates.
pub(super) fn source_bound_split<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
    abi: Option<X86SourceBoundAbi>,
    policy: &SplitPolicy,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    let abi = admitted_abi(abi)?;
    let instructions: usize = source
        .blocks
        .values()
        .map(|block| block.instructions.len())
        .sum();
    if source.blocks.len() > MAX_SPLIT_BLOCKS || instructions > MAX_SPLIT_INSTRUCTIONS {
        return Err(unsupported(X86BodyUnsupported::SourceShape(format!(
            "{} blocks and {instructions} instructions (a function stated in parts has at most \
             {MAX_SPLIT_BLOCKS} and {MAX_SPLIT_INSTRUCTIONS})",
            source.blocks.len()
        ))));
    }
    let rows: usize = machine.blocks.values().map(|block| block.insts.len()).sum();
    if machine.blocks.len() > MAX_SPLIT_BLOCKS || rows > MAX_SPLIT_ROWS {
        return Err(unsupported(X86BodyUnsupported::MachineFunction(format!(
            "{} blocks and {rows} rows (a function stated in parts has at most \
             {MAX_SPLIT_BLOCKS} and {MAX_SPLIT_ROWS})",
            machine.blocks.len()
        ))));
    }
    let frame = admitted_frame(source)?;
    let cfg = source_cfg_bounded(source, MAX_SPLIT_BLOCKS, MAX_SPLIT_INSTRUCTIONS)?;
    check_entry_parameters(source, &frame)?;
    if machine.name != source.name {
        return Err(unsupported(X86BodyUnsupported::MachineFunction(
            "machine and source name different functions".into(),
        )));
    }
    let no_correspondence = |reason: String| {
        unsupported(X86BodyUnsupported::MachineFunction(format!(
            "the machine blocks do not correspond one to one with the LIR blocks: {reason}"
        )))
    };
    // Slice 24a (OD-226): without a block correspondence, the merged-chain
    // quotient the stamps choose is planned, cut and stated instead, from its
    // own frame, control flow and entry parameters, with the original's
    // bounds checked above; with no chain to contract, today's refusal,
    // naming why.
    let reason = match block_correspondence(source, machine, &cfg.dead) {
        Ok(correspondence) => {
            let identity = quotient::Quotient::identity(source, machine);
            return stated_in_parts(source, machine, abi, policy, &identity, cfg, correspondence);
        }
        Err(reason) => reason,
    };
    let quotient = quotient::Quotient::of(source, machine, &cfg)?;
    if quotient.is_identity() {
        // Slice 24c (OD-228): the original pair over its segments, or the
        // refusal naming why there are none.
        let correspondence =
            segment::correspondence(source, machine, &cfg, reason, Some(&quotient))?
                .map_err(no_correspondence)?;
        let segments = correspondence.segments.clone();
        return stated_in_parts(source, machine, abi, policy, &quotient, cfg, correspondence)
            .map_err(|refusal| segments.over(refusal));
    }
    let over = || {
        let (stated, walked) = (quotient.source(), quotient.machine());
        let frame = admitted_frame(stated)?;
        let cfg = source_cfg_bounded(stated, MAX_SPLIT_BLOCKS, MAX_SPLIT_INSTRUCTIONS)?;
        check_entry_parameters(stated, &frame)?;
        let correspondence = match block_correspondence(stated, walked, &cfg.dead) {
            Ok(correspondence) => correspondence,
            // Slice 24c: the quotient pair over its segments.
            Err(reason) => segment::correspondence(stated, walked, &cfg, reason, Some(&quotient))?
                .map_err(no_correspondence)?,
        };
        let segments = correspondence.segments.clone();
        stated_in_parts(source, machine, abi, policy, &quotient, cfg, correspondence)
            .map_err(|refusal| segments.over(refusal))
    };
    over().map_err(|refusal| quotient.over(refusal))
}

/// [`source_bound_split`] from the pair's control flow `cfg` and its block
/// correspondence, over `quotient` (the original pair, or slice 24a's
/// merged-chain quotient): the planned points, the pieces and the regions are
/// the quotient's; every audit coordinate is the ORIGINAL source's, and the
/// result binds the original `source` and `machine`.
fn stated_in_parts<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
    abi: X86SourceBoundAbi,
    policy: &SplitPolicy,
    quotient: &quotient::Quotient<'_>,
    cfg: SourceCfg,
    correspondence: Correspondence,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    let (stated, walked) = (quotient.source(), quotient.machine());
    let original = |block: Block, index: usize| {
        if mutated("audit-in-quotient-coords") {
            (block, index)
        } else {
            quotient.original(block, index)
        }
    };
    // Slice 24c (OD-228): the points whose cut would pair nothing because a
    // segment states them inside its machine block ([`segment::bans`]): a
    // policy's point there refuses by name, and the plan never chooses one.
    let correspondence_segments = correspondence.segments.clone();
    let segment_bans = segment::bans(stated, &cfg, &correspondence_segments);
    // The plan, and the admission of its cut interfaces. A planned cut
    // whose interface refuses (a slot holding different stored private
    // addresses on its edges, an `i128` live across it) is banned and the
    // plan made again without it, at most [`MAX_REPLANS`] times: any cut set
    // with the loop headers is sound, so a different choice only changes
    // what is refused.
    let mut banned: std::collections::BTreeSet<(Block, usize)> = std::collections::BTreeSet::new();
    let (pieces, frame, cfg, sites, loops) = loop {
        // A point in a block no source path reaches cuts no run. A test
        // policy's points are the ORIGINAL source's: each is mapped into the
        // quotient, and a point at a `Jump` the quotient removes (which the
        // original would refuse as a cut in its terminator) refuses.
        let points: Vec<(Block, usize)> = match &policy.points {
            Some(points) => {
                let mut mapped = Vec::with_capacity(points.len());
                for &(block, index) in points {
                    let Some(point) = quotient.to_quotient(block, index) else {
                        return Err(unsupported(X86BodyUnsupported::MachineFunction(format!(
                            "a cut point at the Jump that ends LIR block {block:?}, which the \
                             merged-chain quotient removes"
                        ))));
                    };
                    if let Some(refusal) =
                        segment::banned_point(&correspondence_segments, &segment_bans, point)
                    {
                        return Err(refusal);
                    }
                    if !cfg.dead.contains(&point.0) {
                        mapped.push(point);
                    }
                }
                mapped
            }
            None => {
                // Slice 17: never cut between an indexed access and the
                // guard that bounds it.
                let mut banned = banned.clone();
                banned.extend(indexed::guard_spans(stated, &cfg));
                banned.extend(segment_bans.keys().copied());
                if mutated("plan-over-original") {
                    plan_points(source, &cfg, machine, &correspondence, policy, &banned)?
                } else {
                    plan_points(stated, &cfg, walked, &correspondence, policy, &banned)?
                }
            }
        };
        let pieces = rewrite_pieces(stated, walked, &correspondence, &points, quotient.floor())?;
        let extra = pieces.origin.len();
        let frame = admitted_frame(&pieces.source)?;
        let cut_cfg = source_cfg_bounded(
            &pieces.source,
            MAX_SPLIT_BLOCKS + extra,
            MAX_SPLIT_INSTRUCTIONS + extra,
        )?;
        let position: HashMap<Block, usize> = cut_cfg
            .order
            .iter()
            .enumerate()
            .map(|(i, block)| (*block, i))
            .collect();
        let mut cut_points: Vec<Block> = cut_cfg.cut_points();
        for block in &pieces.cuts {
            if !cut_points.contains(block) {
                cut_points.push(*block);
            }
        }
        cut_points.sort_by_key(|block| position[block]);
        cut_points.dedup();
        if cut_points.len() > policy.max_parts {
            return Err(unsupported(X86BodyUnsupported::SourceShape(format!(
                "{} cut points (a function stated in parts has at most {} regions)",
                cut_points.len(),
                policy.max_parts
            ))));
        }
        let mut sites = SourceSites::default();
        let mut blamed = None;
        // Slice 17: an indexed use a region does not bound blames the region's
        // cut point (a cut that separates a guard from its access).
        let admitted = admitted_cuts(
            &pieces.source,
            &frame,
            &cut_cfg,
            &cut_points,
            &mut sites,
            &mut blamed,
        )
        .and_then(|loops| {
            let programs: Vec<&SourceProgram> = loops
                .regions
                .iter()
                .flat_map(|region| {
                    region
                        .dag
                        .order
                        .iter()
                        .map(|block| &region.dag.blocks[block])
                })
                .collect();
            check_indexed_bounds(&pieces.source, &cut_cfg, None, Some(&loops), &programs).map_err(
                |(start, refusal)| {
                    blamed = start;
                    refusal
                },
            )?;
            Ok(loops)
        });
        match admitted {
            Ok(loops) => break (pieces, frame, cut_cfg, sites, loops),
            Err(refusal) => {
                let point = blamed.map(|block| pieces.original(block, 0));
                match point {
                    Some(point)
                        if policy.points.is_none()
                            && points.contains(&point)
                            && banned.len() < MAX_REPLANS =>
                    {
                        banned.insert(point);
                    }
                    _ => return Err(refusal),
                }
            }
        }
    };
    let extra = pieces.origin.len();
    let body = finish_admission(
        &pieces.source,
        frame,
        &cfg,
        Vec::new(),
        None,
        Some(loops),
        sites,
    )?;
    let mut machine_cfg = machine_skeleton_bounded(
        &pieces.source,
        &pieces.machine,
        &body.machine_slots,
        &body.dead,
        MAX_SPLIT_BLOCKS + extra,
        MAX_SPLIT_ROWS,
    )?;
    // Slice 24c: the pieces keep every segment whole (no point is inside
    // one), so their correspondence is stated over the pieces' segments,
    // chosen and checked on the pieces with the pieces' control flow `cfg`;
    // they must be the segments the bans were derived from (a piece's new
    // block is no member and no exit target of any), else no claim.
    if !correspondence_segments.is_empty() {
        segment::restate(&mut machine_cfg, &pieces.source, &cfg, None)?;
        if let Ok(cut_correspondence) = &machine_cfg.correspondence
            && cut_correspondence.segments != correspondence_segments
        {
            return Err(unsupported(X86BodyUnsupported::Construction(format!(
                "the pieces' segments ({}) are not the segments the cut points were banned \
                 around ({})",
                cut_correspondence.segments.describe(),
                correspondence_segments.describe()
            ))));
        }
    }
    // Each region within the bounds of one part's query.
    if let Ok(cut_correspondence) = &machine_cfg.correspondence {
        let mut block_rows: HashMap<Block, usize> = HashMap::new();
        for (lir, lowered) in &cut_correspondence.lowering {
            block_rows.insert(*lir, pieces.machine.blocks[lowered].insts.len());
        }
        for (dispatch, owner) in &cut_correspondence.dispatch {
            if let Some(lir) = cut_correspondence.origin.get(owner) {
                *block_rows.entry(*lir).or_default() += pieces.machine.blocks[dispatch].insts.len();
            }
        }
        let loops = body.loops.as_ref().expect("a source stated in parts");
        for region in &loops.regions {
            let rows: usize = region
                .dag
                .order
                .iter()
                .map(|block| block_rows.get(block).copied().unwrap_or(0))
                .sum();
            let instructions: usize = region
                .dag
                .order
                .iter()
                .map(|block| pieces.source.blocks[block].instructions.len())
                .sum();
            let blocks = region.dag.order.len();
            if rows > policy.region_rows
                || instructions > policy.region_instructions
                || blocks > policy.region_blocks
            {
                let (start, first) = pieces.original(region.dag.order[0], 0);
                let (start, first) = original(start, first);
                return Err(unsupported(X86BodyUnsupported::SourceShape(format!(
                    "the region from instruction {first} of block {start:?} has {rows} rows, \
                     {instructions} instructions and {blocks} blocks (a part admits {}, {} and {})",
                    policy.region_rows, policy.region_instructions, policy.region_blocks
                ))));
            }
        }
    }
    let walks =
        walk_machine_for_callers(&pieces.source, &body, &machine_cfg, PathEncoding::CANONICAL)?;
    // Slice 23 (OD-205): the theorem, and when it pairs a row, the theorem
    // without the pairing, in its own parts, the arbiter of its refutation
    // ([`super::owner_theorems`]). A statement in parts is checked as each
    // part is, and needs a part: a function whose every part states nothing
    // has no observable (OD-115), and so neither theorem is built for it.
    let (theorem, unpaired) = super::owner_theorems(&body, &walks, |theorem| {
        let construction = |reason| unsupported(X86BodyUnsupported::Construction(reason));
        check_definitional_part(&theorem.obligation, &theorem.free).map_err(construction)?;
        let parts =
            split_parts(&theorem.obligation, &theorem.region_claims).map_err(construction)?;
        if parts.is_empty() {
            return Err(unsupported(X86BodyUnsupported::NoObservable));
        }
        Ok(())
    })?;
    let parts = split_parts(&theorem.obligation, &theorem.region_claims)
        .map_err(|reason| unsupported(X86BodyUnsupported::Construction(reason)))?;
    let paired = theorem.paired;
    let pairing = theorem.pairing;
    let defined_inputs = theorem.defined_inputs;
    let unpaired = unpaired.and_then(|unpaired| {
        let parts = split_parts(&unpaired.obligation, &unpaired.region_claims).ok()?;
        Some(std::sync::Arc::new(super::X86UnpairedTheorem {
            parts: std::sync::Arc::new(X86BodyParts {
                region_claims: unpaired.region_claims,
                parts,
            }),
            obligation: std::sync::Arc::new(unpaired.obligation),
        }))
    });
    // Audit maps, in the original coordinates: each paired call and incoming
    // access once, region by region in each region's block order.
    let loops = body.loops.as_ref().expect("a source stated in parts");
    let loop_walks = walks.loops.as_ref().expect("walked over its regions");
    let mut call_sites: Vec<(Block, usize, usize)> = Vec::new();
    let mut access_sites: Vec<(Block, usize, usize)> = Vec::new();
    let mut bound_rows: Vec<usize> = Vec::new();
    for (region, region_walks) in loops.regions.iter().zip(&loop_walks.regions) {
        for block in &region.dag.order {
            let (program, walk) = (&region.dag.blocks[block], &region_walks.blocks[block]);
            for (source_call, machine_call) in program.calls.iter().zip(&walk.psabi.calls) {
                let (block, index) = pieces.original(source_call.block, source_call.index);
                let (block, index) = original(block, index);
                let site = (block, index, machine_call.row);
                if !call_sites.contains(&site) {
                    call_sites.push(site);
                }
            }
            for (source_access, machine_access) in program.accesses.iter().zip(&walk.psabi.accesses)
            {
                let (block, index) = pieces.original(source_access.block, source_access.index);
                let (block, index) = original(block, index);
                let site = (block, index, machine_access.row);
                if !access_sites.contains(&site) {
                    access_sites.push(site);
                }
            }
            bound_rows.extend(walk.psabi.bound_rows.iter().copied());
        }
    }
    bound_rows.sort_unstable();
    bound_rows.dedup();
    let machine_definitions = std::iter::once(&walks.psabi)
        .chain(walks.clean.as_ref())
        .flat_map(|names| {
            names
                .definitions
                .iter()
                .filter(|(_, _, row)| *row != JOIN_ROW)
                .map(|(name, _, row)| (name.clone(), *row))
        })
        .collect();
    let source_definitions = theorem
        .source_definitions
        .into_iter()
        .map(|(name, block, index)| {
            let (block, index) = pieces.original(block, index);
            let (block, index) = original(block, index);
            (name, block, index)
        })
        .collect();
    let parts = X86BodyParts {
        region_claims: theorem.region_claims,
        parts,
    };
    debug_assert!(parts.check(&theorem.obligation).is_ok());
    Ok(SourceBoundX86Body {
        source,
        machine,
        abi,
        bound_rows,
        source_definitions,
        machine_definitions,
        call_sites,
        access_sites,
        obligation: std::sync::Arc::new(theorem.obligation),
        parts: std::sync::Arc::new(parts),
        fp_abstract: super::rounds(&body, &walks),
        unpaired,
        paired,
        pairing: pairing.filter(|_| paired).map(std::sync::Arc::new),
        routines: body.sites.routines.clone(),
        merged: quotient.merged(),
        segments: correspondence_segments.stated(),
        defined_inputs,
    })
}
