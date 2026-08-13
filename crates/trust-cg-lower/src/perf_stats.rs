//! `TCG_PERF_STATS` — x86 per-function / per-innermost-loop instruction-mix
//! attribution (STEP 0 of `docs/x86-perf-plan.md`).
//!
//! This is the "attribution tool that does not exist yet": it answers, for a
//! hot kernel, *how many x86 instructions per loop iteration does trust-cg
//! emit, and what is the isel-vs-optimizer-vs-regalloc share* — the
//! ground-truth the perf plan's gap estimate needs before any opcode change is
//! committed.
//!
//! INERT BY DEFAULT. Every entry point is a no-op unless the `TCG_PERF_STATS`
//! environment variable is set to a value other than `0`/`false`/`off`. When
//! enabled it only *reads* the emitted machine IR and prints to stderr; it
//! NEVER inspects, reorders, or mutates the instruction stream. An ON-vs-OFF
//! differential is therefore byte-identical by construction (the STEP-0
//! validation criterion).
//!
//! Loop detection is a lightweight back-edge scan (a branch whose target block
//! sits at or before the branching block in layout order), picking the
//! *smallest-span* natural loop — the innermost tight loop of a micro-kernel.
//! It is a diagnostic heuristic, not a verified analysis: nothing on the
//! compile/proof path consumes its output.

use std::collections::HashMap;
use std::fmt;
use std::sync::OnceLock;

use trust_cg_ir::target_info::OpcodeCategory;
use trust_cg_ir::x86_64_ops::X86Opcode;

use crate::instructions::Block;
use crate::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

/// True when `TCG_PERF_STATS` requests attribution output. Evaluated once and
/// cached — the flag is a static property of the process environment.
pub fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| match std::env::var("TCG_PERF_STATS") {
        Ok(v) => {
            let v = v.trim();
            !(v.is_empty()
                || v == "0"
                || v.eq_ignore_ascii_case("false")
                || v.eq_ignore_ascii_case("off"))
        }
        Err(_) => false,
    })
}

/// A non-pseudo x86 instruction-mix histogram over a set of blocks.
///
/// The buckets are the ones the addressing-idiom lever (OPT-7) moves: SIB
/// scaled-index memory ops, `LEA`, and the load-folded arithmetic forms
/// (`add r, [m]` etc.), plus the plain move / load / store traffic that
/// register allocation and two-address fixup inflate.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct InstCounts {
    /// Total non-pseudo machine instructions.
    pub total: usize,
    /// Register-to-register moves (copies): the copy traffic coalescing and
    /// two-address fixup produce.
    pub movrr: usize,
    /// Immediate-to-register moves.
    pub movri: usize,
    /// Loads from memory (all forms, including SIB and load-fold).
    pub loads: usize,
    /// Stores to memory (all forms, including SIB).
    pub stores: usize,
    /// SIB scaled-index loads (`mov r, [base + idx*scale + disp]`).
    pub sib_load: usize,
    /// SIB scaled-index stores.
    pub sib_store: usize,
    /// `LEA r, [base + disp]`.
    pub lea: usize,
    /// `LEA r, [base + idx*scale + disp]` (SIB form).
    pub lea_sib: usize,
    /// Load-folded arithmetic/compare (`add`/`sub`/`imul`/`cmp`/`test` r, [m]).
    pub load_fold: usize,
    /// Register-register integer multiplies (the LEA-for-mul-by-const target).
    pub imul_rr: usize,
    /// Shift-left-by-immediate (the strength-reduced-index recompute).
    pub shl_ri: usize,
}

impl InstCounts {
    fn account(&mut self, inst: &X86ISelInst) {
        let op = inst.opcode;
        if op.is_pseudo() {
            return;
        }
        self.total += 1;
        match op {
            X86Opcode::MovRR
            | X86Opcode::MovRR32
            | X86Opcode::MovsdRR
            | X86Opcode::MovssRR
            | X86Opcode::MovdqaRR => self.movrr += 1,
            X86Opcode::MovRI => self.movri += 1,
            X86Opcode::MovRMSib => {
                self.sib_load += 1;
                self.loads += 1;
            }
            X86Opcode::MovMRSib => {
                self.sib_store += 1;
                self.stores += 1;
            }
            X86Opcode::Lea => self.lea += 1,
            X86Opcode::LeaSib => self.lea_sib += 1,
            X86Opcode::AddRM
            | X86Opcode::SubRM
            | X86Opcode::ImulRM
            | X86Opcode::CmpRM
            | X86Opcode::TestRM => {
                self.load_fold += 1;
                self.loads += 1;
            }
            X86Opcode::ImulRR => self.imul_rr += 1,
            X86Opcode::ShlRI => self.shl_ri += 1,
            other => match other.categorize() {
                OpcodeCategory::Load => self.loads += 1,
                OpcodeCategory::Store => self.stores += 1,
                _ => {}
            },
        }
    }
}

impl fmt::Display for InstCounts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "insts={} movrr={} movri={} loads={} stores={} sib_load={} sib_store={} \
             lea={} lea_sib={} load_fold={} imul_rr={} shl_ri={}",
            self.total,
            self.movrr,
            self.movri,
            self.loads,
            self.stores,
            self.sib_load,
            self.sib_store,
            self.lea,
            self.lea_sib,
            self.load_fold,
            self.imul_rr,
            self.shl_ri,
        )
    }
}

/// Count the non-pseudo instruction mix of the whole function.
pub fn count_function(func: &X86ISelFunction) -> InstCounts {
    let mut counts = InstCounts::default();
    for block in func.block_order.iter().filter_map(|b| func.blocks.get(b)) {
        for inst in &block.insts {
            counts.account(inst);
        }
    }
    counts
}

/// Count the non-pseudo instruction mix over a specific set of blocks (e.g. a
/// detected loop body). Blocks absent from the function are skipped.
pub fn count_blocks(func: &X86ISelFunction, blocks: &[Block]) -> InstCounts {
    let mut counts = InstCounts::default();
    for block in blocks.iter().filter_map(|b| func.blocks.get(b)) {
        for inst in &block.insts {
            counts.account(inst);
        }
    }
    counts
}

/// Detect the innermost natural loop and return its body blocks in layout
/// order, or `None` when the function has no back-edge (straight-line code).
///
/// A back-edge is any branch operand `Block(target)` (or CFG successor) whose
/// layout-order position is at or before the branching block. The loop body is
/// the contiguous layout-order span `[header, tail]`. "Innermost" = smallest
/// span (ties resolve to the first found). This relies on unresolved `Block`
/// branch operands, so callers on the codegen side must detect the body BEFORE
/// `resolve_x86_branches` rewrites branch targets to numeric offsets.
pub fn innermost_loop_body(func: &X86ISelFunction) -> Option<Vec<Block>> {
    let pos: HashMap<Block, usize> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, b)| (*b, i))
        .collect();

    let mut best: Option<(usize, usize)> = None; // (header_pos, tail_pos)
    let consider = |header_pos: usize, tail_pos: usize, best: &mut Option<(usize, usize)>| {
        if header_pos > tail_pos {
            return;
        }
        let span = tail_pos - header_pos;
        match best {
            Some((bh, bt)) if (*bt - *bh) <= span => {}
            _ => *best = Some((header_pos, tail_pos)),
        }
    };

    for (tail_pos, blk) in func.block_order.iter().enumerate() {
        let Some(block) = func.blocks.get(blk) else {
            continue;
        };
        for inst in &block.insts {
            for operand in &inst.operands {
                if let X86ISelOperand::Block(target) = operand
                    && let Some(&header_pos) = pos.get(target)
                {
                    consider(header_pos, tail_pos, &mut best);
                }
            }
        }
        for target in &block.successors {
            if let Some(&header_pos) = pos.get(target) {
                consider(header_pos, tail_pos, &mut best);
            }
        }
    }

    best.map(|(hp, tp)| func.block_order[hp..=tp].to_vec())
}

/// Format a compact human/greppable label for a loop body block list.
pub fn loop_label(blocks: &[Block]) -> String {
    let ids: Vec<String> = blocks.iter().map(|b| format!("b{}", b.0)).collect();
    format!("[{}]", ids.join(","))
}

/// Build the per-function post-ISel attribution report (called from the isel
/// finalize chokepoint). `mir_inst_count` is the summed trust-ir instruction
/// count the selector consumed, giving the pre-isel-MIR-vs-post-isel-x86 ratio.
pub fn isel_report(func: &X86ISelFunction, mir_inst_count: usize) -> String {
    let whole = count_function(func);
    let mut out = format!(
        "TCG_PERF_STATS stage=isel fn={} mir_insts={} {}\n",
        func.name, mir_inst_count, whole,
    );
    if let Some(body) = innermost_loop_body(func) {
        let loop_counts = count_blocks(func, &body);
        out.push_str(&format!(
            "TCG_PERF_STATS stage=isel fn={} loop={} {}",
            func.name,
            loop_label(&body),
            loop_counts,
        ));
    } else {
        out.push_str(&format!(
            "TCG_PERF_STATS stage=isel fn={} loop=none",
            func.name
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86_64_isel::{X86ISelBlock, X86ISelInst};

    fn func_with_blocks(blocks: Vec<(Block, X86ISelBlock)>) -> X86ISelFunction {
        use crate::function::Signature;
        let mut f = X86ISelFunction::new(
            "t".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        for (id, b) in blocks {
            f.block_order.push(id);
            f.blocks.insert(id, b);
        }
        f
    }

    fn inst(op: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, operands)
    }

    #[test]
    fn counts_addressing_idioms() {
        let mut b = X86ISelBlock::default();
        b.insts.push(inst(X86Opcode::MovRR, vec![]));
        b.insts.push(inst(X86Opcode::ImulRR, vec![]));
        b.insts.push(inst(X86Opcode::MovRMSib, vec![]));
        b.insts.push(inst(X86Opcode::AddRM, vec![]));
        b.insts.push(inst(X86Opcode::Lea, vec![]));
        let f = func_with_blocks(vec![(Block(0), b)]);
        let c = count_function(&f);
        assert_eq!(c.total, 5);
        assert_eq!(c.movrr, 1);
        assert_eq!(c.imul_rr, 1);
        assert_eq!(c.sib_load, 1);
        assert_eq!(c.loads, 2); // sib_load + add_rm load-fold
        assert_eq!(c.load_fold, 1);
        assert_eq!(c.lea, 1);
    }

    #[test]
    fn detects_innermost_self_loop() {
        // b0 -> b1 -> (b1 back-edge) -> b2
        let mut b0 = X86ISelBlock::default();
        b0.insts
            .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]));
        let mut b1 = X86ISelBlock::default();
        b1.insts.push(inst(X86Opcode::AddRR, vec![]));
        // conditional back-edge to itself, else fall to b2
        b1.insts
            .push(inst(X86Opcode::Jcc, vec![X86ISelOperand::Block(Block(1))]));
        let b2 = X86ISelBlock::default();
        let f = func_with_blocks(vec![(Block(0), b0), (Block(1), b1), (Block(2), b2)]);
        let body = innermost_loop_body(&f).expect("loop");
        assert_eq!(body, vec![Block(1)]);
    }

    #[test]
    fn no_loop_when_forward_only() {
        let mut b0 = X86ISelBlock::default();
        b0.insts
            .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]));
        let b1 = X86ISelBlock::default();
        let f = func_with_blocks(vec![(Block(0), b0), (Block(1), b1)]);
        assert!(innermost_loop_body(&f).is_none());
    }
}
