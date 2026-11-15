// trust-cg-codegen/pipeline_branch_relax_tests.rs - relaxed branches pass the
// final-stream authority and encode as the standard relaxation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Post-allocation AArch64 functions whose conditional branch spans more than
//! its encoding range go through the public [`resolve_branches`] and then
//! every encode route, including the proof-grade one that forces the
//! final-stream nets (resolved-CFG reconstruction, post-RA recheck,
//! reaching-definition, frame dataflow) and the decode check to Enforce. Each
//! must accept the relaxed stream. Direct-tail cases use a complemented
//! branch and `B` to the original target; a dispatch tail stays in place and
//! its unchanged conditional reaches a nearby `B` island. Before relaxation
//! existed, these functions were refused by the encoder with
//! `branch offset … out of signed 19-bit range` (14-bit for TBZ).

use super::*;
use trust_cg_ir::function::{Signature, Type};
use trust_cg_ir::regs::{X0, X9, X30};

/// A real jump-table dispatch with an arm large enough to put either its
/// default branch or its local table beyond one-word PC-relative reach.
fn large_table_dispatch(forward: bool) -> IrMachFunction {
    large_table_dispatch_with_filler(forward, (IMM19_REACH + 2) as usize)
}

fn large_table_dispatch_with_filler(forward: bool, filler_words: usize) -> IrMachFunction {
    use trust_cg_ir::function::JumpTableData;
    use trust_cg_ir::regs::X10;
    let mut f = function(if forward {
        "far_table_forward"
    } else {
        "far_table_backward"
    });
    let entry = f.entry;
    let arm0 = f.create_block();
    let arm1 = f.create_block();
    let default = f.create_block();
    let dispatch = if forward {
        entry
    } else {
        let dispatch = f.create_block();
        f.block_order = vec![entry, default, arm0, arm1, dispatch];
        add(
            &mut f,
            entry,
            IrMachInst::new(IrOpcode::B, vec![IrOperand::Block(dispatch)]),
        );
        dispatch
    };
    for (op, operands) in [
        (IrOpcode::CmpRI, vec![preg(X0), IrOperand::Imm(1)]),
        (
            IrOpcode::BCond,
            vec![IrOperand::Imm(8), IrOperand::Block(default)],
        ),
        (IrOpcode::Adr, vec![preg(X9), IrOperand::JumpTableIndex(0)]),
        (IrOpcode::LdrswRO, vec![preg(X10), preg(X9), preg(X0)]),
        (IrOpcode::AddRR, vec![preg(X9), preg(X9), preg(X10)]),
        (IrOpcode::Br, vec![preg(X9)]),
    ] {
        add(&mut f, dispatch, IrMachInst::new(op, operands));
    }
    f.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![arm0, arm1],
    });
    movz(&mut f, arm0, X0, 17);
    ret(&mut f, arm0);
    filler(&mut f, arm1, filler_words);
    movz(&mut f, arm1, X0, 731);
    ret(&mut f, arm1);
    movz(&mut f, default, X0, 99);
    ret(&mut f, default);
    if forward && filler_words == (IMM19_REACH - 9) as usize {
        let default_word: usize = f
            .block_order
            .iter()
            .take_while(|&&block| block != default)
            .map(|&block| f.block(block).insts.len())
            .sum();
        let table_word: usize = f
            .block_order
            .iter()
            .map(|&block| f.block(block).insts.len())
            .sum();
        assert_eq!(default_word - 1, IMM19_REACH as usize);
        assert_eq!(table_word - 2, 1 << 18);
    }
    finish(f)
}

#[test]
fn far_dispatch_keeps_bounds_and_address_binding_through_every_encode_route() {
    for (forward, filler_words) in [
        (false, (IMM19_REACH + 2) as usize),
        (true, (IMM19_REACH + 2) as usize),
        // The conditional is initially exactly at its positive limit:
        // 6 dispatch words + 2 arm0 words + (filler_words + 2) arm1 words,
        // minus the conditional's one-word position = IMM19_REACH words.
        // The ADR's ADD insertion alone pushes it out of range. Branch
        // relaxation must therefore run AGAIN before final resolution.
        (true, (IMM19_REACH - 9) as usize),
    ] {
        let f = large_table_dispatch_with_filler(forward, filler_words);
        assert_eq!(f.jump_table_address_expansions.len(), usize::from(forward));
        if forward {
            assert_eq!(f.blocks.len(), 5, "the conditional needs its near island");
        }
        let words = encode_everywhere(&f);
        assert!(words.len() > 1 << 18);
        let (_, _, map) = encode_function_with_fixups_and_blocks(&f).unwrap();
        let bytes: Vec<_> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        crate::aarch64::layout_crosscheck::check_final_layout(&f, &bytes, None, &map, true)
            .unwrap();
        let report =
            trust_cg_verify::aarch64_switch_binding::check_aarch64_switch_dispatch(&f, &bytes)
                .unwrap();
        assert_eq!((report.jump_tables, report.table_entries), (1, 2));

        #[cfg(target_arch = "aarch64")]
        {
            // Engineering execution only. The checks above independently
            // enforce the real final words/layout; no proof grade is donated.
            let buffer = crate::jit::JitCompiler::new(crate::jit::JitConfig {
                opt_level: OptLevel::O0,
                ..Default::default()
            })
            .compile_raw(std::slice::from_ref(&f), &std::collections::HashMap::new())
            .unwrap();
            // SAFETY: the tracked signature is exactly one u64 in and out;
            // buffer owns the executable mapping throughout these calls.
            let run: extern "C" fn(u64) -> u64 =
                unsafe { buffer.get_fn_bound(&f.name).unwrap().into_inner() };
            for (selector, expected) in [(0, 17), (1, 731), (2, 99), (u64::MAX, 99)] {
                assert_eq!(
                    run(selector),
                    expected,
                    "forward={forward}, filler_words={filler_words}, selector={selector}"
                );
            }
        }
    }
}

#[test]
fn recomputed_wrong_address_intent_or_missing_custody_still_refuses() {
    let good = large_table_dispatch(true);
    encode_everywhere(&good);
    let (&adr, row) = good.jump_table_address_expansions.iter().next().unwrap();
    for mutation in 0..5 {
        let mut bad = good.clone();
        match mutation {
            0 => {
                if let IrOperand::Imm(high) = &mut bad.inst_mut(row.add).operands[2] {
                    *high += 1;
                }
            }
            1 => {
                if let IrOperand::Imm(low) = &mut bad.inst_mut(adr).operands[1] {
                    *low ^= 4;
                }
            }
            2 => {
                bad.jump_table_address_expansions.clear();
            }
            3 => bad.inst_mut(row.add).operands[1] = preg(X0),
            4 => bad.inst_mut(row.add).opcode = IrOpcode::SubRI,
            _ => unreachable!(),
        }
        // Re-encode the mutated intent, not merely a stale/hash-corrupted
        // object. Independent table layout/bounds must still disagree.
        assert!(encode_function(&bad).is_err(), "mutation {mutation}");
    }
}

#[cfg(target_arch = "aarch64")]
#[test]
fn block_profile_splices_refuse_a_long_address_before_rewriting_its_bytes() {
    use crate::jit::{JitCompiler, JitConfig, ProfileHookMode};
    let f = large_table_dispatch(true);
    for mode in [
        ProfileHookMode::BlockCounts,
        ProfileHookMode::BlockCountsAndTiming,
    ] {
        let error = JitCompiler::new(JitConfig {
            profile_hooks: mode,
            ..Default::default()
        })
        .compile_raw(std::slice::from_ref(&f), &std::collections::HashMap::new())
        .expect_err("post-splice long-address relation is not modeled yet");
        assert!(
            error.to_string().contains("modeled post-splice re-layout"),
            "{error}"
        );
    }
}

/// B.cond / CBZ / CBNZ reach +/-2^18 instructions.
const IMM19_REACH: i64 = (1 << 18) - 1;
/// TBZ / TBNZ reach +/-2^13 instructions.
const IMM14_REACH: i64 = (1 << 13) - 1;

fn add(func: &mut IrMachFunction, block: BlockId, inst: IrMachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

fn preg(reg: trust_cg_ir::regs::PReg) -> IrOperand {
    IrOperand::PReg(reg)
}

fn movz(func: &mut IrMachFunction, block: BlockId, reg: trust_cg_ir::regs::PReg, value: i64) {
    add(
        func,
        block,
        IrMachInst::new(IrOpcode::Movz, vec![preg(reg), IrOperand::Imm(value)]),
    );
}

fn ret(func: &mut IrMachFunction, block: BlockId) {
    add(
        func,
        block,
        IrMachInst::new(IrOpcode::Ret, vec![preg(X30)]).with_implicit_uses(&[X0]),
    );
}

/// `count` instructions of `x9 += 1` (x9 is defined first, so the
/// reaching-definition net sees every read defined).
fn filler(func: &mut IrMachFunction, block: BlockId, count: usize) {
    movz(func, block, X9, 0);
    for _ in 1..count {
        add(
            func,
            block,
            IrMachInst::new(IrOpcode::AddRI, vec![preg(X9), preg(X9), IrOperand::Imm(1)]),
        );
    }
}

fn function(name: &str) -> IrMachFunction {
    IrMachFunction::new(
        name.to_string(),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    )
}

fn finish(mut func: IrMachFunction) -> IrMachFunction {
    rebuild_ir_cfg_edges_from_branch_operands(&mut func);
    resolve_branches(&mut func).expect("an out-of-range branch is relaxed, not refused");
    func
}

/// Encode through every route and check they agree byte for byte; return
/// the words.
fn encode_everywhere(func: &IrMachFunction) -> Vec<u32> {
    let code = encode_function(func).expect("encode_function accepts the relaxed stream");
    let (with_fixups, _) =
        encode_function_with_fixups(func).expect("encode_function_with_fixups accepts it");
    assert_eq!(with_fixups, code);
    for pipeline in [
        Pipeline::new(PipelineConfig::for_host_aarch64()),
        Pipeline::new(PipelineConfig::for_host_aarch64()).with_proof_grade_aarch64_publication(),
    ] {
        let (policy, _) = encode_function_with_fixups_for_pipeline(&pipeline, func)
            .expect("the policy-aware route (proof-grade: every net enforced) accepts it");
        assert_eq!(policy, code);
    }
    code.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// Signed immediate of `bits` bits at `shift` in `word`.
fn field(word: u32, shift: u32, bits: u32) -> i64 {
    let raw = (word >> shift) & ((1 << bits) - 1);
    let sign = 1i64 << (bits - 1);
    (raw as i64 ^ sign) - sign
}

/// `B.cond` word: condition and signed instruction offset.
fn b_cond(word: u32) -> (u32, i64) {
    assert_eq!(
        word & 0xFF00_0010,
        0x5400_0000,
        "{word:#010x} is not B.cond"
    );
    (word & 0xF, field(word, 5, 19))
}

/// `B` word: signed instruction offset.
fn b(word: u32) -> i64 {
    assert_eq!(word & 0xFC00_0000, 0x1400_0000, "{word:#010x} is not B");
    field(word, 0, 26)
}

#[test]
fn a_far_b_cond_encodes_as_the_complement_skipping_a_b_to_the_target() {
    // entry: cmp x0, #0 ; b.eq far
    // near:  <filler> ; movz x0, #2 ; ret
    // far:   movz x0, #7 ; ret
    let fill = (IMM19_REACH + 1) as usize;
    let mut func = function("relax_b_cond_far");
    let entry = func.entry;
    let near = func.create_block();
    let far = func.create_block();
    add(
        &mut func,
        entry,
        IrMachInst::new(IrOpcode::CmpRI, vec![preg(X0), IrOperand::Imm(0)]),
    );
    add(
        &mut func,
        entry,
        IrMachInst::new(
            IrOpcode::BCond,
            vec![IrOperand::Imm(0), IrOperand::Block(far)],
        ),
    );
    filler(&mut func, near, fill);
    movz(&mut func, near, X0, 2);
    ret(&mut func, near);
    movz(&mut func, far, X0, 7);
    ret(&mut func, far);
    let func = finish(func);
    let words = encode_everywhere(&func);

    // [cmp, b.ne +2, b far] [fill, movz, ret] [movz #7, ret]
    assert_eq!(words.len(), 3 + fill + 2 + 2);
    assert_eq!(b_cond(words[1]), (1, 2), "b.ne skips the B into `near`");
    let far_word = 3 + fill as i64 + 2;
    assert_eq!(b(words[2]), far_word - 2, "B reaches `far`");
    // Unrelaxed, `far` began at word 2 + fill + 2, seen from the b.eq at 1.
    assert!(
        2 + fill as i64 + 2 - 1 > IMM19_REACH,
        "the original b.eq was out of range"
    );
}

#[test]
fn a_far_tbz_encodes_as_tbnz_skipping_a_b_to_the_target() {
    // entry: tbz x0, #5, far   near: <filler>; movz; ret   far: movz; ret
    let fill = (IMM14_REACH + 1) as usize;
    let mut func = function("relax_tbz_far");
    let entry = func.entry;
    let near = func.create_block();
    let far = func.create_block();
    add(
        &mut func,
        entry,
        IrMachInst::new(
            IrOpcode::Tbz,
            vec![preg(X0), IrOperand::Imm(5), IrOperand::Block(far)],
        ),
    );
    filler(&mut func, near, fill);
    movz(&mut func, near, X0, 2);
    ret(&mut func, near);
    movz(&mut func, far, X0, 7);
    ret(&mut func, far);
    let func = finish(func);
    let words = encode_everywhere(&func);

    // TBNZ x0, #5, +2  (b5=0, op=1, b40=5, imm14=2, Rt=0)
    let tbnz = words[0];
    assert_eq!(tbnz & 0x7F00_0000, 0x3700_0000, "{tbnz:#010x} is not TBNZ");
    assert_eq!((tbnz >> 19) & 0x1F, 5, "same tested bit");
    assert_eq!(tbnz & 0x1F, 0, "same register");
    assert_eq!(field(tbnz, 5, 14), 2);
    let far_word = 2 + fill as i64 + 2;
    assert_eq!(b(words[1]), far_word - 1);
}

#[test]
fn a_far_cbz_back_edge_encodes_as_cbnz_skipping_a_b_back() {
    // entry: movz x9... falls into body
    // body:  <filler>                     (the loop body)
    // latch: cbz x0, body                 (far back-edge; falls into exit)
    // exit:  movz x0, #2 ; ret
    // A backward imm19 reaches one instruction further (-2^18): go past it.
    let fill = (IMM19_REACH + 2) as usize;
    let mut func = function("relax_cbz_back_edge");
    let entry = func.entry;
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    movz(&mut func, entry, X9, 0);
    filler(&mut func, body, fill);
    add(
        &mut func,
        latch,
        IrMachInst::new(IrOpcode::Cbz, vec![preg(X0), IrOperand::Block(body)]),
    );
    movz(&mut func, exit, X0, 2);
    ret(&mut func, exit);
    let func = finish(func);
    let words = encode_everywhere(&func);

    // [movz] [fill] [cbnz x0, +2 ; b body] [movz, ret]
    let latch_word = 1 + fill;
    let cbnz = words[latch_word];
    assert_eq!(cbnz & 0x7F00_0000, 0x3500_0000, "{cbnz:#010x} is not CBNZ");
    assert_eq!(field(cbnz, 5, 19), 2);
    assert_eq!(b(words[latch_word + 1]), 1 - (latch_word as i64 + 1));
}

#[test]
fn both_targets_far_splits_into_a_trampoline_block_the_authority_accepts() {
    // entry: b body
    // done0: movz x0, #7 ; ret                  (far behind the latch)
    // body:  <filler>                            (falls into latch)
    // latch: cmp x0, #0 ; b.eq done0 ; b done1  (both far)
    // pad:   <filler> ; movz x0, #2 ; ret
    // done1: movz x0, #3 ; ret                  (far ahead of the latch)
    let fill = (IMM19_REACH + 1) as usize;
    let mut func = function("relax_split");
    let entry = func.entry;
    let done0 = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let pad = func.create_block();
    let done1 = func.create_block();
    add(
        &mut func,
        entry,
        IrMachInst::new(IrOpcode::B, vec![IrOperand::Block(body)]),
    );
    movz(&mut func, done0, X0, 7);
    ret(&mut func, done0);
    filler(&mut func, body, fill);
    add(
        &mut func,
        latch,
        IrMachInst::new(IrOpcode::CmpRI, vec![preg(X0), IrOperand::Imm(0)]),
    );
    add(
        &mut func,
        latch,
        IrMachInst::new(
            IrOpcode::BCond,
            vec![IrOperand::Imm(0), IrOperand::Block(done0)],
        ),
    );
    add(
        &mut func,
        latch,
        IrMachInst::new(IrOpcode::B, vec![IrOperand::Block(done1)]),
    );
    filler(&mut func, pad, fill);
    movz(&mut func, pad, X0, 2);
    ret(&mut func, pad);
    movz(&mut func, done1, X0, 3);
    ret(&mut func, done1);
    let blocks_before = func.blocks.len();
    let func = finish(func);
    assert_eq!(func.blocks.len(), blocks_before + 1, "one trampoline block");
    let words = encode_everywhere(&func);

    // [b] [movz, ret] [fill] [cmp, b.ne +2, b done0] [b done1] [fill, movz, ret] [movz, ret]
    let latch_word = 1 + 2 + fill;
    assert_eq!(b_cond(words[latch_word + 1]), (1, 2));
    assert_eq!(b(words[latch_word + 2]), 1 - (latch_word as i64 + 2));
    let done1_word = latch_word + 4 + fill + 2;
    assert_eq!(
        b(words[latch_word + 3]),
        done1_word as i64 - (latch_word as i64 + 3)
    );
    assert_eq!(words.len(), done1_word + 2);
}

#[test]
fn an_in_range_function_resolves_exactly_as_before() {
    // The same shape one instruction inside the b.eq's reach: no relaxation,
    // so the branch stays a single b.eq straight to `far`.
    let fill = (IMM19_REACH - 3) as usize;
    let mut func = function("in_range");
    let entry = func.entry;
    let near = func.create_block();
    let far = func.create_block();
    add(
        &mut func,
        entry,
        IrMachInst::new(IrOpcode::CmpRI, vec![preg(X0), IrOperand::Imm(0)]),
    );
    add(
        &mut func,
        entry,
        IrMachInst::new(
            IrOpcode::BCond,
            vec![IrOperand::Imm(0), IrOperand::Block(far)],
        ),
    );
    filler(&mut func, near, fill);
    movz(&mut func, near, X0, 2);
    ret(&mut func, near);
    movz(&mut func, far, X0, 7);
    ret(&mut func, far);
    let func = finish(func);
    let words = encode_everywhere(&func);
    assert_eq!(words.len(), 2 + fill + 2 + 2);
    assert_eq!(
        b_cond(words[1]),
        (0, IMM19_REACH),
        "b.eq at exactly its reach"
    );
}
