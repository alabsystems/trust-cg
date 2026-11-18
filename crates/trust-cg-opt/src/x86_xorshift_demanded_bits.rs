// trust-cg-opt - x86-64 demanded-bits rewrite for the xorshift idiom
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Demanded-bits rewrite for `y = x ^ (x << k)` on x86-64.
//!
//! Shifting left by `k` cannot change bits below `k`, so
//!
//! ```text
//!     y = x ^ (x << k)   =>   y[i] == x[i]  for all i < k
//! ```
//!
//! A consumer that reads ONLY bits `[0, k)` of `y` may therefore read `x`. The
//! rewrite removes no instruction — `y` is still computed — it SHORTENS THE
//! DEPENDENCY CHAIN feeding that consumer by one shift-and-xor.
//!
//! # DEFAULT ON since 2026-10-01, on this measurement
//!
//! `b1_mispredict`, 120 interleaved rounds, `taskset -c 2`, min statistic, both
//! arms carried twice as byte-identical copies:
//!
//! ```text
//!     llvm   189.907 ms   1.0000
//!     off    208.113 ms   1.0959      <- the old default
//!     off2   208.233 ms   1.0965      <- floor 0.0006
//!     on     194.839 ms   1.0260
//!     on2    194.628 ms   1.0249      <- floor 0.0011
//! ```
//!
//! The 0.070 effect is ~60x the larger floor, and the suite harness
//! independently reports b1 at 1.025 with the pass on. All 18 programs MATCH and
//! `library/core` at O3 is unchanged (0 failed roots / 1284 objects).
//!
//! # Why this is worth a pass, and why the payoff is latency
//!
//! `b1_mispredict`'s loop is `s ^= s<<13; s ^= s>>7; s ^= s<<17`, and the branch
//! choosing its two arms tests `s & 1` — bit 0 of the FINAL value. This backend
//! computes that predicate from `s3`; LLVM computes it from `s2`, one dependent
//! operation earlier, and `s3 = s2 ^ (s2 << 17)` so bits 0..16 agree.
//!
//! b1's cost is wrong-path work executed in a mispredicted shadow, so resolving
//! a 50%-mispredicting branch one ALU op sooner is the point. **This is a
//! latency claim, not an instruction-count claim** — the extra xor is free on an
//! out-of-order core, but the branch cannot resolve until its input does. The
//! AArch64 twin ([`crate::xorshift_demanded_bits`], default-ON) credits exactly
//! this at -9ms of b1's 29ms gap there, independently reproduced at -11ms.
//!
//! # Why this is a separate pass from the AArch64 one, not a registration
//!
//! Three differences, each of which would make a direct port fire on NOTHING:
//!
//! 1. **Different IR universe.** x86 passes implement [`X86MachinePass`] over
//!    `X86ISelFunction`/`X86ISelInst`; the AArch64 pass takes `MachFunction`.
//! 2. **No shift-fused xor.** AArch64's producer is ONE instruction,
//!    `EorRRLsl dst, a, a, #k`, and the recognizer is "both source registers are
//!    the same". x86 has no such form: the producer is the PAIR
//!    `ShlRI t, x, k` + `XorRR y, x, t`.
//! 3. **x86 ISel vregs are NOT SSA, and the operands do not match
//!    syntactically.** Measured from b1's actual pre-RA stream
//!    (`-Ztrust-ir-cg-args=trace-peephole-entry`):
//!
//!    ```text
//!      MovRR v25, v24
//!      ShlRI v28, v25, 17        <- shifts v25
//!      XorRR v29, v24, v28       <- xors  v24   (NOT v25)
//!      MovRR v30, v29
//!      BtRI  v30, 0              <- reads v30   (NOT v29)
//!    ```
//!
//!    A recognizer demanding `ShlRI`'s source to equal `XorRR`'s other operand
//!    matches nothing, and a consumer scan keyed on the xor's `dst` matches
//!    nothing. Both sides must be resolved through `MovRR` copy chains.
//!
//! # Correctness
//!
//! The rewrite is a pure in-place OPERAND SUBSTITUTION: no instruction is
//! created, deleted, merged or moved, no flag behaviour changes, and the
//! substituted operand is a USE slot in every accepted shape.
//!
//! Two independent conditions carry it, and both fail closed:
//!
//! * **The bit range.** Every demanded bit must lie strictly below `k`
//!   (`hi < k`). Reading a bit at or above `k` from `x` instead of `y` is a
//!   WRONG VALUE, so this inequality is the whole value argument. Any consumer
//!   shape this pass does not recognize yields `None` and is left alone.
//! * **Single-def-ness, which SSA gave the AArch64 twin for free.** Every vreg
//!   on a resolved copy chain, and `x` itself, must have exactly ONE definition
//!   function-wide. That makes the substituted value stable: `x`'s single def is
//!   an operand-producer of `y`'s def, `y`'s def dominates the consumer (else
//!   the program as given is already invalid), so every path reaching the
//!   consumer has passed `x`'s def and `x` still holds the value the identity
//!   was proven about. Without this, a loop-carried merge vreg could be
//!   redefined between the producer and the consumer and the substitution would
//!   read the NEXT iteration's value.
//!
//! The pass is also idempotent, which matters because at O3 the x86 pass manager
//! runs `run_to_fixpoint`: it only ever rewrites a use toward a STRICTLY EARLIER
//! def, nothing in the x86 schedule rewrites a use back toward a later def, and
//! a rewritten operand names `x`, which is not itself a producer `dst` of the
//! same chain — so the second iteration finds nothing and reports no change.
//!
//! # Deliberately NOT done
//!
//! Only `ShlRI` producers (a LEFT shift by a constant). A right shift preserves
//! the HIGH bits, which no x86 consumer in the accepted table demands, and a
//! variable shift amount has no static `k`.

use crate::fast_hash::FxHashMap as HashMap;

use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_pass_manager::X86MachinePass;

static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the FORENSIC OPT-OUT from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=no-x86-xorshift-demanded-bits`). The pass is DEFAULT ON
/// since 2026-10-01, on the measurement in the module doc.
pub fn set_x86_xorshift_demanded_bits_disabled(disabled: bool) -> bool {
    match DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => DISABLED.get() == Some(&requested),
    }
}

fn enabled() -> bool {
    if DISABLED.get().copied().unwrap_or(false) {
        return false;
    }
    !crate::tcg_env_flag("TCG_NO_X86_XORSHIFT_DEMANDED_BITS")
}

/// Install the trace (`-Ztrust-ir-cg-args=trace-x86-xorshift-demanded-bits`).
pub fn set_x86_xorshift_demanded_bits_trace_enabled(enabled: bool) -> bool {
    match TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => TRACE.get() == Some(&requested),
    }
}

/// Should the pipeline REGISTER this pass? DEFAULT ON, so it is part of the
/// default x86 schedule and the two pipeline tests that pin that schedule name
/// it. The opt-out removes the pass entirely rather than leaving a no-op behind.
pub fn x86_xorshift_demanded_bits_registered() -> bool {
    enabled()
}

fn trace_enabled() -> bool {
    TRACE.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_XORSHIFT_DB_TRACE")
}

/// Count definitions of every vreg across the whole function.
///
/// x86 ISel output is NOT SSA — loop-carried merge vregs are genuinely
/// multi-def — so this is the substitute for the SSA property the AArch64 twin
/// relies on. Operand 0 of a value-producing opcode is the def slot; a
/// def-and-use opcode (`AndRI [v, v, imm]` and friends) still DEFINES operand 0
/// and is counted.
fn def_counts(func: &X86ISelFunction) -> HashMap<VReg, u32> {
    use crate::effects::x86_produces_value;
    let mut counts: HashMap<VReg, u32> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if !x86_produces_value(inst.opcode) {
                continue;
            }
            if let Some(X86ISelOperand::VReg(d)) = inst.operands.first() {
                *counts.entry(*d).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// `MovRR dst, src` chains, as dst -> src, for single-def `dst` AND single-def
/// `src` only. A multi-def link makes the chain's value position-dependent, and
/// this pass has no liveness, so such a link is refused rather than traversed.
fn copy_links(func: &X86ISelFunction, defs: &HashMap<VReg, u32>) -> HashMap<VReg, VReg> {
    let mut links: HashMap<VReg, VReg> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if inst.opcode != X86Opcode::MovRR {
                continue;
            }
            let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
            else {
                continue;
            };
            if d.class != s.class {
                continue;
            }
            if defs.get(d).copied() != Some(1) || defs.get(s).copied() != Some(1) {
                continue;
            }
            links.insert(*d, *s);
        }
    }
    links
}

/// Follow `MovRR` links to the chain's root. Bounded so a malformed cyclic chain
/// cannot hang the compiler.
fn copy_root(v: VReg, links: &HashMap<VReg, VReg>) -> VReg {
    let mut cur = v;
    for _ in 0..64 {
        match links.get(&cur) {
            Some(next) if *next != cur => cur = *next,
            _ => return cur,
        }
    }
    cur
}

/// Highest bit index this instruction reads from operand `op_idx`, or `None`
/// when the demanded range cannot be bounded — which must be treated as "all
/// bits" and declined.
///
/// Every accepted slot is a pure USE. `BtRI`/`TestRI` produce no value (they are
/// flag-setters), so their operand 0 is a use; `AndRI`'s operand 1 is a use
/// whether or not operand 0 names the same vreg.
fn highest_demanded_bit(inst: &X86ISelInst, op_idx: usize) -> Option<u32> {
    let imm = |i: usize| -> Option<i64> {
        match inst.operands.get(i) {
            Some(X86ISelOperand::Imm(v)) => Some(*v),
            _ => None,
        }
    };
    let top_set_bit = |m: i64| -> Option<u32> {
        let m = m as u64;
        if m == 0 {
            return None;
        }
        Some(63 - m.leading_zeros())
    };
    match inst.opcode {
        // BT src, #b — reads exactly bit b.
        X86Opcode::BtRI if op_idx == 0 && inst.operands.len() == 2 => u32::try_from(imm(1)?).ok(),
        // TEST src, #mask — reads exactly the mask's set bits.
        X86Opcode::TestRI if op_idx == 0 && inst.operands.len() == 2 => top_set_bit(imm(1)?),
        // AND dst, src, #mask — three-operand form only; operand 1 is the use.
        X86Opcode::AndRI if op_idx == 1 && inst.operands.len() == 3 => top_set_bit(imm(2)?),
        _ => None,
    }
}

/// x86-64 xorshift demanded-bits pass. See the module docs.
pub struct X86XorshiftDemandedBits;

impl X86MachinePass for X86XorshiftDemandedBits {
    fn name(&self) -> &str {
        "x86-xorshift-demanded-bits"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        if !enabled() {
            return false;
        }
        run_scoped(func, trace_enabled())
    }
}

/// Run regardless of the install gate (the tests' entry point).
pub fn run_on_function(func: &mut X86ISelFunction) -> bool {
    run_scoped(func, trace_enabled())
}

fn run_scoped(func: &mut X86ISelFunction, trace: bool) -> bool {
    let defs = def_counts(func);
    let links = copy_links(func, &defs);

    // Producers: the xor's def (by copy-root) -> (x, k), for the PAIR
    // `ShlRI t, x', k` + `XorRR y, x, t` where x' and x share a copy root.
    let mut shifts: HashMap<VReg, (VReg, u32)> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if inst.opcode != X86Opcode::ShlRI || inst.operands.len() != 3 {
                continue;
            }
            let (
                Some(X86ISelOperand::VReg(t)),
                Some(X86ISelOperand::VReg(src)),
                Some(X86ISelOperand::Imm(k)),
            ) = (
                inst.operands.first(),
                inst.operands.get(1),
                inst.operands.get(2),
            )
            else {
                continue;
            };
            // SHL masks its immediate modulo the destination's carrier width.
            // The identity below uses an actual shift by k, so admit only a
            // canonical nonzero count and matching scalar register views.
            // In particular, a raw count of 64 on a Gpr64 shifts by zero:
            // x ^ (x << 64) is zero, and cannot be replaced by x at bit 0.
            let width = match t.class {
                trust_cg_ir::regs::RegClass::Gpr32 => 32,
                trust_cg_ir::regs::RegClass::Gpr64 => 64,
                _ => continue,
            };
            let Ok(k) = u32::try_from(*k) else { continue };
            if src.class != t.class || k == 0 || k >= width || defs.get(t).copied() != Some(1) {
                continue;
            }
            shifts.insert(*t, (copy_root(*src, &links), k));
        }
    }

    let mut producers: HashMap<VReg, (VReg, u32)> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if inst.opcode != X86Opcode::XorRR || inst.operands.len() != 3 {
                continue;
            }
            let (
                Some(X86ISelOperand::VReg(y)),
                Some(X86ISelOperand::VReg(a)),
                Some(X86ISelOperand::VReg(b)),
            ) = (
                inst.operands.first(),
                inst.operands.get(1),
                inst.operands.get(2),
            )
            else {
                continue;
            };
            if y.class != a.class || y.class != b.class || defs.get(y).copied() != Some(1) {
                continue;
            }
            // Either source may be the shift temp (XOR is commutative).
            for (temp, other) in [(b, a), (a, b)] {
                let Some(&(x, k)) = shifts.get(temp) else {
                    continue;
                };
                // The shifted value and the xor's other operand must be the
                // SAME value: genuinely `x ^ (x << k)`.
                if copy_root(*other, &links) != x {
                    continue;
                }
                // `x` must be single-def, or the substituted read is not stable.
                if defs.get(&x).copied() != Some(1) {
                    continue;
                }
                producers.insert(*y, (x, k));
                break;
            }
        }
    }
    if producers.is_empty() {
        return false;
    }

    let mut changed = false;
    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get(&block_id) else {
            continue;
        };
        let n = block.insts.len();
        for idx in 0..n {
            for op_idx in 0..func.blocks[&block_id].insts[idx].operands.len() {
                let inst = &func.blocks[&block_id].insts[idx];
                let Some(X86ISelOperand::VReg(used)) = inst.operands.get(op_idx).cloned() else {
                    continue;
                };
                let root = copy_root(used, &links);
                let Some(&(x, k)) = producers.get(&root) else {
                    continue;
                };
                if x == used {
                    continue; // already reads x
                }
                let Some(hi) = highest_demanded_bit(inst, op_idx) else {
                    continue;
                };
                // The whole value argument: every demanded bit strictly below k.
                if hi >= k {
                    if trace {
                        eprintln!(
                            "x86-xorshift-db[{}/{:?}]: declined {:?} op{op_idx} — demands bit \
                             {hi} but the identity only covers bits < {k}",
                            func.name, block_id, inst.opcode
                        );
                    }
                    continue;
                }
                let opcode = inst.opcode;
                func.blocks.get_mut(&block_id).expect("checked").insts[idx].operands[op_idx] =
                    X86ISelOperand::VReg(x);
                changed = true;
                if trace {
                    eprintln!(
                        "x86-xorshift-db[{}/{:?}]: {opcode:?} op{op_idx} now reads {x:?} \
                         instead of {used:?} (demands bits < {hi}+1, identity covers < {k})",
                        func.name, block_id
                    );
                }
            }
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;

    fn g(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn vr(v: VReg) -> X86ISelOperand {
        X86ISelOperand::VReg(v)
    }
    fn imm(i: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(i)
    }
    fn inst(op: X86Opcode, ops: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, ops)
    }

    fn func_with(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("db_test".to_string(), sig);
        f.ensure_block(Block(0));
        let b = f.blocks.get_mut(&Block(0)).unwrap();
        b.insts = insts;
        b.insts.push(inst(X86Opcode::Ret, vec![]));
        f
    }

    /// b1's EXACT measured shape, copies included:
    ///   MovRR v25, v24 ; ShlRI v28, v25, 17 ; XorRR v29, v24, v28
    ///   MovRR v30, v29 ; BtRI v30, 0
    fn b1_shape(bit: i64, shift: i64) -> X86ISelFunction {
        func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::MovRR, vec![vr(g(25)), vr(g(24))]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(25)), imm(shift)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            inst(X86Opcode::MovRR, vec![vr(g(30)), vr(g(29))]),
            inst(X86Opcode::BtRI, vec![vr(g(30)), imm(bit)]),
        ])
    }

    fn operand(f: &X86ISelFunction, idx: usize, op: usize) -> Option<VReg> {
        match f.blocks[&Block(0)].insts[idx].operands.get(op)? {
            X86ISelOperand::VReg(v) => Some(*v),
            _ => None,
        }
    }

    #[test]
    fn rewrites_b1s_bit_test_through_both_copy_chains() {
        let mut f = b1_shape(0, 17);
        assert!(run_on_function(&mut f), "b1's measured shape must fire");
        assert_eq!(
            operand(&f, 5, 0),
            Some(g(24)),
            "BtRI must read x (v24) directly, not the copy of the xor's result"
        );
        // Nothing else moved: the xor still computes v29 from v24 and v28.
        assert_eq!(operand(&f, 3, 0), Some(g(29)));
        assert_eq!(operand(&f, 3, 1), Some(g(24)));
        assert_eq!(operand(&f, 3, 2), Some(g(28)));
        assert_eq!(
            f.blocks[&Block(0)].insts.len(),
            7,
            "no instruction added or removed"
        );
    }

    #[test]
    fn is_idempotent_so_the_o3_fixpoint_terminates() {
        let mut f = b1_shape(0, 17);
        assert!(run_on_function(&mut f));
        assert!(
            !run_on_function(&mut f),
            "a second iteration must report no change, or the O3 fixpoint churns"
        );
    }

    #[test]
    fn declines_a_bit_at_the_shift_amount() {
        // bit 17 is NOT covered by a shift of 17: y[17] != x[17] in general.
        let mut f = b1_shape(17, 17);
        assert!(!run_on_function(&mut f));
        assert_eq!(operand(&f, 5, 0), Some(g(30)), "operand untouched");
    }

    #[test]
    fn declines_a_bit_above_the_shift_amount() {
        let mut f = b1_shape(40, 17);
        assert!(!run_on_function(&mut f));
    }

    #[test]
    fn rewrites_the_and_mask_form_when_every_set_bit_is_below_k() {
        // b1's second site: AndRI v97, v95, 6 where v95 copies the xor's result.
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(24)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            inst(X86Opcode::MovRR, vec![vr(g(95)), vr(g(29))]),
            inst(X86Opcode::AndRI, vec![vr(g(97)), vr(g(95)), imm(6)]),
        ]);
        assert!(run_on_function(&mut f));
        assert_eq!(
            operand(&f, 4, 1),
            Some(g(24)),
            "the mask's use slot reads x"
        );
        assert_eq!(operand(&f, 4, 0), Some(g(97)), "the DEF slot is untouched");
    }

    #[test]
    fn declines_an_and_mask_reaching_at_or_above_k() {
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(24)), imm(4)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            // mask 0x18 = bits 3..4; bit 4 is NOT below k=4.
            inst(X86Opcode::AndRI, vec![vr(g(97)), vr(g(29)), imm(0x18)]),
        ]);
        assert!(!run_on_function(&mut f));
    }

    #[test]
    fn declines_a_right_shift_producer() {
        // `x ^ (x >> k)` preserves the HIGH bits, not the low ones.
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::ShrRI, vec![vr(g(28)), vr(g(24)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            inst(X86Opcode::BtRI, vec![vr(g(29)), imm(0)]),
        ]);
        assert!(!run_on_function(&mut f));
    }

    #[test]
    fn declines_a_two_source_xor_that_merely_carries_a_shift() {
        // `a ^ (b << k)` with a != b proves nothing about a's low bits.
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::MovRI, vec![vr(g(26)), imm(9)]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(26)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            inst(X86Opcode::BtRI, vec![vr(g(29)), imm(0)]),
        ]);
        assert!(!run_on_function(&mut f));
    }

    #[test]
    fn declines_when_x_is_multi_def() {
        // THE non-SSA guard. If `x` is redefined, reading it at the consumer can
        // observe a different value than the identity was proven about — on b1
        // that would be the NEXT iteration's seed.
        let mut f = b1_shape(0, 17);
        {
            let b = f.blocks.get_mut(&Block(0)).unwrap();
            // a second def of v24, after the consumer
            b.insts
                .insert(6, inst(X86Opcode::MovRI, vec![vr(g(24)), imm(99)]));
        }
        assert!(
            !run_on_function(&mut f),
            "a multi-def x must be refused: SSA is what the AArch64 twin relies on"
        );
        assert_eq!(operand(&f, 5, 0), Some(g(30)));
    }

    #[test]
    fn declines_when_a_copy_on_the_chain_is_multi_def() {
        let mut f = b1_shape(0, 17);
        {
            let b = f.blocks.get_mut(&Block(0)).unwrap();
            // v30 (the consumer's copy) gets a second def
            b.insts
                .insert(5, inst(X86Opcode::MovRI, vec![vr(g(30)), imm(5)]));
        }
        assert!(!run_on_function(&mut f));
    }

    #[test]
    fn never_touches_the_two_operand_and_rmw_form() {
        // `AndRI [v, imm]` (2 operands) has operand 0 as BOTH def and use;
        // rewriting it would change the value WRITTEN.
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(24)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(24)), vr(g(28))]),
            inst(X86Opcode::AndRI, vec![vr(g(29)), imm(6)]),
        ]);
        assert!(!run_on_function(&mut f));
        assert_eq!(operand(&f, 3, 0), Some(g(29)), "the RMW slot is untouched");
    }

    #[test]
    fn accepts_the_commuted_xor_operand_order() {
        // `XorRR y, t, x` — the shift temp first.
        let mut f = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(24)), imm(7)]),
            inst(X86Opcode::ShlRI, vec![vr(g(28)), vr(g(24)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(29)), vr(g(28)), vr(g(24))]),
            inst(X86Opcode::BtRI, vec![vr(g(29)), imm(3)]),
        ]);
        assert!(run_on_function(&mut f));
        assert_eq!(operand(&f, 3, 0), Some(g(24)));
    }

    #[test]
    fn declines_a_zero_shift() {
        let mut f = b1_shape(0, 0);
        assert!(!run_on_function(&mut f));
    }

    /// The hardware masks a count at or above its carrier width. For x=1,
    /// counts 32/64 at their own widths make y=0 (bit 0 differs from x), and
    /// count 65 makes y=3 (bit 1 differs from x). Raw k is not the identity's
    /// effective shift amount, so these consumers must stay on y.
    #[test]
    fn declines_noncanonical_shift_counts_at_both_carrier_widths() {
        for (class, shift, bit) in [
            (RegClass::Gpr32, 32, 0),
            (RegClass::Gpr32, 64, 0),
            (RegClass::Gpr32, 65, 1),
            (RegClass::Gpr64, 64, 0),
            (RegClass::Gpr64, 65, 1),
        ] {
            let v = |id| VReg::new(id, class);
            let mut f = func_with(vec![
                inst(X86Opcode::MovRI, vec![vr(v(0)), imm(1)]),
                inst(X86Opcode::ShlRI, vec![vr(v(1)), vr(v(0)), imm(shift)]),
                inst(X86Opcode::XorRR, vec![vr(v(2)), vr(v(0)), vr(v(1))]),
                inst(X86Opcode::BtRI, vec![vr(v(2)), imm(bit)]),
            ]);
            assert!(
                !run_on_function(&mut f),
                "rewrote {class:?} shift={shift} bit={bit}"
            );
            assert_eq!(operand(&f, 3, 0), Some(v(2)));
        }
    }

    /// A count of 32 is an ordinary nonzero shift for a 64-bit carrier. The
    /// conservative count guard must retain that valid optimization.
    #[test]
    fn retains_a_valid_64_bit_shift_by_32() {
        let mut f = b1_shape(31, 32);
        assert!(run_on_function(&mut f));
        assert_eq!(operand(&f, 5, 0), Some(g(24)));
    }

    /// The count's carrier is determined by the shift destination, and the
    /// xor identity requires the same register view on both producer steps.
    #[test]
    fn declines_mismatched_shift_and_xor_register_widths() {
        let narrow = |id| VReg::new(id, RegClass::Gpr32);
        let mut wrong_shift_view = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(0)), imm(1)]),
            inst(X86Opcode::ShlRI, vec![vr(narrow(1)), vr(g(0)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(g(2)), vr(g(0)), vr(narrow(1))]),
            inst(X86Opcode::BtRI, vec![vr(g(2)), imm(0)]),
        ]);
        assert!(!run_on_function(&mut wrong_shift_view));
        assert_eq!(operand(&wrong_shift_view, 3, 0), Some(g(2)));

        let mut wrong_xor_view = func_with(vec![
            inst(X86Opcode::MovRI, vec![vr(g(0)), imm(1)]),
            inst(X86Opcode::ShlRI, vec![vr(g(1)), vr(g(0)), imm(17)]),
            inst(X86Opcode::XorRR, vec![vr(narrow(2)), vr(g(0)), vr(g(1))]),
            inst(X86Opcode::BtRI, vec![vr(narrow(2)), imm(0)]),
        ]);
        assert!(!run_on_function(&mut wrong_xor_view));
        assert_eq!(operand(&wrong_xor_view, 3, 0), Some(narrow(2)));
    }
}
