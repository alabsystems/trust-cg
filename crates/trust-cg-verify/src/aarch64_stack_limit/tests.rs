// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `[TCG-A64-STACK-LIMIT]` net on hand-built final streams: acceptance,
//! every named mutation control, elision, the module bound and the lemma.

use super::*;
use trust_cg_ir::Signature;
use trust_cg_ir::aarch64_regs::{X0, X1, X16, X17, X29, X30, XZR};
use trust_cg_ir::function::{MachStackLimit, StackLimitRequest};

fn mk(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn reg(p: PReg) -> MachOperand {
    MachOperand::PReg(p)
}

fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}

fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

fn lo(block: u32) -> MachInst {
    mk(
        AArch64Opcode::BCond,
        vec![imm(COND_LO), MachOperand::Block(BlockId(block))],
    )
}

/// The shapes a test builds; each field is one knob a mutation turns.
#[derive(Clone)]
struct Shape {
    source: StackLimitSource,
    overflow: StackLimitOverflow,
    /// The frame the body allocates below the callee-saved area.
    frame: u32,
    /// The `F` the check compares against (normally `frame`).
    compare: u32,
    cond: i64,
    /// The register the SUBS subtracts.
    subtrahend: PReg,
    /// Instructions inserted between the FP setup and the check.
    before_check: Vec<MachInst>,
    /// Instructions inserted at the head of the overflow block.
    overflow_extra: Vec<MachInst>,
    handler_symbol: String,
    trap_imm: i64,
}

impl Shape {
    fn handler() -> Self {
        Self {
            source: StackLimitSource::Pointee { offset: 8 },
            overflow: StackLimitOverflow::Handler {
                symbol: "on_overflow".to_string(),
            },
            frame: 32,
            compare: 32,
            cond: COND_LO,
            subtrahend: X17,
            before_check: Vec::new(),
            overflow_extra: Vec::new(),
            handler_symbol: "on_overflow".to_string(),
            trap_imm: i64::from(STACK_LIMIT_TRAP_IMM),
        }
    }

    fn limit(&self) -> MachStackLimit {
        MachStackLimit {
            request: StackLimitRequest {
                param: 0,
                source: self.source,
                overflow: self.overflow.clone(),
            },
            limit_reg: X0,
            arg_regs: vec![X0, X1],
        }
    }

    /// The frame insertion shape: the entry block ends with the first
    /// `B.LO`, a second block holds the frame compare and ends with the
    /// second, and the body follows; block 1 is the overflow block.
    fn build(&self) -> MachFunction {
        let mut func = MachFunction::new("requester".to_string(), Signature::new(vec![], vec![]));
        let overflow = func.create_block();
        let wide = self.compare != 0;
        let second = if wide {
            Some(func.create_block())
        } else {
            None
        };
        let body = func.create_block();
        let mut entry = vec![
            mk(
                AArch64Opcode::StpPreIndex,
                vec![reg(X29), reg(X30), sp(), imm(-16)],
            ),
            mk(AArch64Opcode::AddRI, vec![reg(X29), sp(), imm(0)]),
        ];
        entry.extend(self.before_check.iter().cloned());
        if let StackLimitSource::Pointee { offset } = self.source {
            entry.push(mk(
                AArch64Opcode::LdrRI,
                vec![reg(X17), reg(X0), imm(i64::from(offset))],
            ));
        }
        entry.push(mk(
            AArch64Opcode::SubsRR,
            vec![
                if wide { reg(X16) } else { reg(XZR) },
                sp(),
                reg(self.subtrahend),
            ],
        ));
        entry.push(mk(
            AArch64Opcode::BCond,
            vec![imm(self.cond), MachOperand::Block(overflow)],
        ));
        let mut second_insts = Vec::new();
        if wide {
            if self.compare <= 4095 {
                second_insts.push(mk(
                    AArch64Opcode::CmpRI,
                    vec![reg(X16), imm(i64::from(self.compare))],
                ));
            } else {
                second_insts.push(mk(
                    AArch64Opcode::Movz,
                    vec![reg(X17), imm(i64::from(self.compare & 0xFFFF))],
                ));
                if self.compare >> 16 != 0 {
                    second_insts.push(mk(
                        AArch64Opcode::Movk,
                        vec![reg(X17), imm(i64::from(self.compare >> 16)), imm(16)],
                    ));
                }
                second_insts.push(mk(AArch64Opcode::CmpRR, vec![reg(X16), reg(X17)]));
            }
            second_insts.push(lo(overflow.0));
        }
        let mut body_insts = Vec::new();
        if self.frame != 0 {
            let mut left = self.frame;
            while left > 0 {
                let chunk = left.min(4080);
                body_insts.push(mk(
                    AArch64Opcode::SubRI,
                    vec![sp(), sp(), imm(i64::from(chunk))],
                ));
                left -= chunk;
            }
            body_insts.push(mk(AArch64Opcode::StrRI, vec![reg(X1), sp(), imm(8)]));
            let mut left = self.frame;
            while left > 0 {
                let chunk = left.min(4080);
                body_insts.push(mk(
                    AArch64Opcode::AddRI,
                    vec![sp(), sp(), imm(i64::from(chunk))],
                ));
                left -= chunk;
            }
        }
        body_insts.push(mk(
            AArch64Opcode::LdpPostIndex,
            vec![reg(X29), reg(X30), sp(), imm(16)],
        ));
        body_insts.push(mk(AArch64Opcode::Ret, vec![]));
        let mut tail: Vec<MachInst> = self.overflow_extra.clone();
        match &self.overflow {
            StackLimitOverflow::Trap => {
                tail.push(mk(AArch64Opcode::Brk, vec![imm(self.trap_imm)]));
            }
            StackLimitOverflow::Handler { .. } => {
                tail.push(mk(
                    AArch64Opcode::LdpPostIndex,
                    vec![reg(X29), reg(X30), sp(), imm(16)],
                ));
                tail.push(mk(
                    AArch64Opcode::TailCall,
                    vec![MachOperand::Symbol(self.handler_symbol.clone())],
                ));
            }
        }
        let fill = |func: &mut MachFunction, block: BlockId, insts: Vec<MachInst>| {
            for inst in insts {
                let id = func.push_inst(inst);
                func.append_inst(block, id);
            }
        };
        fill(&mut func, BlockId(0), entry);
        fill(&mut func, overflow, tail);
        fill(&mut func, body, body_insts);
        func.add_edge(BlockId(0), overflow);
        match second {
            Some(second) => {
                fill(&mut func, second, second_insts);
                func.add_edge(BlockId(0), second);
                func.add_edge(second, overflow);
                func.add_edge(second, body);
            }
            None => func.add_edge(BlockId(0), body),
        }
        func.stack_limit = Some(self.limit());
        func.stack_limit_overflow_block = Some(overflow);
        func
    }
}

fn refused(shape: &Shape) -> StackLimitViolation {
    check(&shape.build()).expect_err("the mutation must be refused")
}

#[test]
fn present_checks_are_certified_for_both_sources_and_modes() {
    for shape in [
        Shape::handler(),
        Shape {
            source: StackLimitSource::Value,
            subtrahend: X0,
            ..Shape::handler()
        },
        Shape {
            overflow: StackLimitOverflow::Trap,
            ..Shape::handler()
        },
        Shape {
            frame: 0,
            compare: 0,
            ..Shape::handler()
        },
        Shape {
            frame: 64 * 1024 + 16,
            compare: 64 * 1024 + 16,
            ..Shape::handler()
        },
    ] {
        let certificate = check(&shape.build()).unwrap().unwrap();
        let StackLimitOutcome::Checked(checked) = certificate.outcome else {
            panic!("expected a present check");
        };
        assert_eq!(checked.csa, 16);
        assert_eq!(checked.sp_adj, shape.frame);
        assert_eq!(checked.total, 16 + shape.frame);
        assert_eq!(checked.deepest, 16 + shape.frame);
        assert_eq!(checked.overflow_block, BlockId(1));
        assert!(!checked.check_insts.is_empty());
    }
}

#[test]
fn a_short_total_is_refused() {
    let error = refused(&Shape {
        compare: 16,
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::FrameDepth, "{error}");
}

#[test]
fn every_wrong_condition_is_refused() {
    for cond in [
        0b1011, /* LT */
        0b0010, /* HS */
        0b0000, /* EQ */
    ] {
        let error = refused(&Shape {
            cond,
            ..Shape::handler()
        });
        assert_eq!(error.kind, StackLimitViolationKind::CheckShape, "{error}");
    }
}

#[test]
fn a_wrong_source_is_refused() {
    let error = refused(&Shape {
        subtrahend: X1,
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::CheckShape, "{error}");
    // Value source declared, Pointee load emitted.
    let mut shape = Shape::handler();
    let mut func = shape.build();
    if let Some(limit) = func.stack_limit.as_mut() {
        limit.request.source = StackLimitSource::Value;
    }
    assert!(check(&func).is_err());
    // Pointee offset differs.
    shape.source = StackLimitSource::Pointee { offset: 16 };
    let mut func = shape.build();
    if let Some(limit) = func.stack_limit.as_mut() {
        limit.request.source = StackLimitSource::Pointee { offset: 8 };
    }
    assert!(check(&func).is_err());
}

#[test]
fn code_before_the_check_is_refused() {
    // The limit register redefined before the check.
    let error = refused(&Shape {
        before_check: vec![mk(AArch64Opcode::Movz, vec![reg(X0), imm(0)])],
        ..Shape::handler()
    });
    assert!(
        matches!(
            error.kind,
            StackLimitViolationKind::PreCheckCode | StackLimitViolationKind::CheckShape
        ),
        "{error}"
    );
    // An SP decrement (the check moved late).
    let error = refused(&Shape {
        before_check: vec![mk(AArch64Opcode::SubRI, vec![sp(), sp(), imm(16)])],
        ..Shape::handler()
    });
    assert!(
        matches!(
            error.kind,
            StackLimitViolationKind::PreCheckCode | StackLimitViolationKind::CheckShape
        ),
        "{error}"
    );
    // A call before the check.
    let error = refused(&Shape {
        before_check: vec![mk(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("f".to_string())],
        )],
        ..Shape::handler()
    });
    assert!(
        matches!(
            error.kind,
            StackLimitViolationKind::PreCheckCode | StackLimitViolationKind::CheckShape
        ),
        "{error}"
    );
}

#[test]
fn the_check_deleted_is_refused() {
    let mut func = Shape::handler().build();
    // Drop the SUBS and its branch: the body runs unchecked.
    let entry = &mut func.blocks[0].insts;
    entry.drain(3..5);
    assert!(check(&func).is_err());
    // Drop the frame compare and its branch instead.
    let mut func = Shape::handler().build();
    func.blocks[2].insts.clear();
    assert!(check(&func).is_err());
}

#[test]
fn a_bad_overflow_path_is_refused() {
    // A storing overflow path.
    let error = refused(&Shape {
        overflow_extra: vec![mk(AArch64Opcode::StrRI, vec![reg(X1), sp(), imm(0)])],
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::OverflowPath, "{error}");
    // An overflow path that lowers SP.
    let error = refused(&Shape {
        overflow_extra: vec![mk(AArch64Opcode::SubRI, vec![sp(), sp(), imm(16)])],
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::OverflowPath, "{error}");
    // A wrong handler.
    let error = refused(&Shape {
        handler_symbol: "someone_else".to_string(),
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::OverflowPath, "{error}");
    // A wrong trap immediate.
    let error = refused(&Shape {
        overflow: StackLimitOverflow::Trap,
        trap_imm: 1,
        ..Shape::handler()
    });
    assert_eq!(error.kind, StackLimitViolationKind::OverflowPath, "{error}");
    // The overflow block reachable from the body too.
    let mut func = Shape::handler().build();
    let body = BlockId(3);
    func.add_edge(body, BlockId(1));
    assert_eq!(
        check(&func).unwrap_err().kind,
        StackLimitViolationKind::OverflowPath
    );
}

#[test]
fn cleared_or_altered_fields_are_refused() {
    let shape = Shape::handler();
    // The overflow-block record cleared: the elision rule refuses a frame.
    let mut func = shape.build();
    func.stack_limit_overflow_block = None;
    assert!(check(&func).is_err());
    // The requirement cleared on the function: custody refuses it.
    let mut func = shape.build();
    func.stack_limit = None;
    assert!(check_against(&func, &shape.limit()).is_err());
    // An entry block that is a branch target.
    let mut func = shape.build();
    let loop_block = func.create_block();
    func.add_edge(loop_block, BlockId(0));
    assert_eq!(
        check(&func).unwrap_err().kind,
        StackLimitViolationKind::PreCheckCode
    );
}

#[test]
fn a_frameless_requester_is_certified_as_elided_only_without_stack_use() {
    let mut func = MachFunction::new("leaf".to_string(), Signature::new(vec![], vec![]));
    let ret = func.push_inst(mk(AArch64Opcode::Ret, vec![]));
    func.append_inst(BlockId(0), ret);
    func.stack_limit = Some(Shape::handler().limit());
    let certificate = check(&func).unwrap().unwrap();
    assert_eq!(certificate.outcome, StackLimitOutcome::Elided);
    // Stack use without a check is refused.
    let store = func.push_inst(mk(AArch64Opcode::StrRI, vec![reg(X1), sp(), imm(-8)]));
    func.blocks[0].insts.insert(0, store);
    assert!(check(&func).is_err());
}

#[test]
fn frame_depth_follows_sp_and_frame_addresses() {
    let func = Shape::handler().build();
    assert_eq!(frame_depth(&func).unwrap(), 48);
    let mut func = MachFunction::new("addr".to_string(), Signature::new(vec![], vec![]));
    for inst in [
        mk(AArch64Opcode::SubRI, vec![sp(), sp(), imm(64)]),
        // x16 = sp + 0x2000 - 0x2020 = CFA - 96, then a store through it.
        mk(AArch64Opcode::Movz, vec![reg(X16), imm(0x20)]),
        mk(AArch64Opcode::SubRR, vec![reg(X17), sp(), reg(X16)]),
        mk(AArch64Opcode::StrRI, vec![reg(X1), reg(X17), imm(0)]),
        mk(AArch64Opcode::AddRI, vec![sp(), sp(), imm(64)]),
        mk(AArch64Opcode::Ret, vec![]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(BlockId(0), id);
    }
    assert_eq!(frame_depth(&func).unwrap(), 96);
}

#[test]
fn entry_demand_actual_checked_facts_preserve_external_handler_diagnostic() {
    let requester = Shape::handler().build();
    let certificate = check(&requester).unwrap().unwrap();
    let requester_facts = function_stack_facts(&requester, Some(&certificate));
    assert_eq!(requester_facts.frame, Some(48));
    assert!(requester_facts.direct_callees.contains("on_overflow"));
    assert_eq!(
        entry_stack_demand(std::slice::from_ref(&requester_facts), "requester"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::UnboundOverflowHandler {
            function: "requester".to_string(),
            handler: "on_overflow".to_string(),
        })
    );

    let mut handler = MachFunction::new("on_overflow".to_string(), Signature::new(vec![], vec![]));
    let ret = handler.push_inst(mk(AArch64Opcode::Ret, vec![]));
    handler.append_inst(BlockId(0), ret);
    let handler_facts = function_stack_facts(&handler, None);
    assert_eq!(handler_facts.frame, Some(0));
    assert_eq!(
        entry_stack_demand(&[requester_facts, handler_facts], "requester"),
        EntryStackDemand::Fixed {
            bytes: 48,
            external_assumptions: BTreeMap::new(),
        }
    );
}

fn facts(name: &str, role: StackRole, frame: u32, callees: &[&str]) -> FunctionStackFacts {
    FunctionStackFacts {
        name: name.to_string(),
        role,
        frame: Some(frame),
        direct_callees: callees.iter().map(|c| c.to_string()).collect(),
        indirect_call: false,
    }
}

#[test]
fn the_module_bound_counts_unchecked_chains_handlers_and_imports() {
    let checked = |handler: Option<&str>| StackRole::Checked {
        csa: 16,
        handler: handler.map(str::to_string),
    };
    let functions = vec![
        facts("f", checked(Some("h")), 64, &["g", "f"]),
        facts("h", StackRole::Plain, 32, &[]),
        facts("g", StackRole::Plain, 48, &["memcpy"]),
    ];
    // f's own D is max(csa 16, handler 32); its callee g reaches 48 + A.
    let bound = module_bound(&functions, 100);
    assert_eq!(bound.reserve, Some(148));
    assert_eq!(bound.external_allowance, 100);
    // A cycle among unchecked functions is unbounded, never a number.
    let functions = vec![
        facts("f", checked(None), 64, &["g"]),
        facts("g", StackRole::Plain, 48, &["k"]),
        facts("k", StackRole::Plain, 16, &["g"]),
    ];
    let bound = module_bound(&functions, 0);
    assert_eq!(bound.reserve, None);
    assert!(bound.unbounded_reason.unwrap().contains("cycle"));
    // Recursion through a checked requester is bounded.
    let functions = vec![
        facts("f", checked(None), 64, &["g"]),
        facts("g", StackRole::Plain, 48, &["f"]),
    ];
    assert_eq!(module_bound(&functions, 0).reserve, Some(64));
    // An indirect call counts every emitted function and the allowance.
    let mut caller = facts("f", checked(None), 64, &[]);
    caller.indirect_call = true;
    let functions = vec![caller, facts("big", StackRole::Plain, 4096, &[])];
    assert_eq!(module_bound(&functions, 8).reserve, Some(4096));
    // A frame the model cannot bound makes R unbounded.
    let mut unknown = facts("g", StackRole::Plain, 0, &[]);
    unknown.frame = None;
    let functions = vec![facts("f", checked(None), 64, &["g"]), unknown];
    assert_eq!(module_bound(&functions, 0).reserve, None);
}

/// The lemma at 8 bits, exhaustively (a test: the 64-bit statement is a
/// different theorem, carried by the solver gate).
#[test]
fn lemma_holds_exhaustively_at_eight_bits() {
    for p in 0..=u8::MAX {
        for l in 0..=u8::MAX {
            for f in 0..=u8::MAX {
                let branches = p < l || p.wrapping_sub(l) < f;
                let reference = u16::from(p) < u16::from(l) + u16::from(f);
                assert_eq!(branches, reference, "p={p} l={l} f={f}");
            }
        }
    }
}

/// The 64-bit lemma on edge cases and a deterministic sample (statistical
/// evidence: a test, never a proof).
#[test]
fn lemma_holds_on_sampled_64_bit_inputs() {
    let edges = [
        0u64,
        1,
        15,
        16,
        4095,
        4096,
        1 << 32,
        u64::MAX / 2,
        u64::MAX - 1,
        u64::MAX,
    ];
    for &p in &edges {
        for &l in &edges {
            for &f in &edges {
                assert_eq!(
                    lemma_branches(p, l, f),
                    lemma_reference(p, l, f),
                    "{p} {l} {f}"
                );
            }
        }
    }
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..200_000 {
        let (p, l) = (next(), next());
        let f = next() >> (next() % 64);
        assert_eq!(
            lemma_branches(p, l, f),
            lemma_reference(p, l, f),
            "{p} {l} {f}"
        );
        // Near the boundary.
        let l = p.wrapping_sub(f).wrapping_add(next() % 3).wrapping_sub(1);
        assert_eq!(
            lemma_branches(p, l, f),
            lemma_reference(p, l, f),
            "{p} {l} {f}"
        );
    }
}
