// Unit tests for the loop-state contract: one table, run over both machine IRs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{BlockId, MachInst, RegClass, Signature, X86CondCode};
use trust_cg_lower::function::Signature as X86Signature;
use trust_cg_lower::instructions::Block;

/// Register numbers shared by both IRs' fixtures.
const IV: u32 = 10;
const ACC: u32 = 11;
const N: u32 = 12;
const T: u32 = 13;
const MERGE: u32 = 14;
const TMP: u32 = 15;
const LAST: u32 = 16;
const NEXT: u32 = 17;
const LEN: u32 = 18;
const STOP: u32 = 19;
const OUT: u32 = 20;
const BASE: u32 = 21;
/// The fixtures' loop bound, `N`'s constant.
const BOUND: i64 = 64;

/// One row of the table: a loop shape and the set the rewrite reproduces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Row {
    /// Only the induction is carried. Admitted with `[iv]`.
    IvOnly,
    /// An accumulator the rewrite reproduces. Admitted with `[iv, acc]`.
    IvAcc,
    /// The same loop, but the rewrite reproduces only `iv`: `acc` is carried
    /// and not reproduced. Refused.
    AccNotReproduced,
    /// The count-if diamond: `merge` is written on both arms and read by the
    /// latch writeback in the same iteration. Admitted with `[iv, acc]`.
    CountIfMerge,
    /// A second accumulator `t += iv`. Refused (`t` into the header).
    SecondAccumulator,
    /// `last = iv`, read only after the loop. Refused: live into the header
    /// through the header's exit edge.
    LiveOutTemporary,
    /// A rotated (bottom-tested) loop with `last = iv` read after the loop.
    /// `last` is written before any read on entry to the header, so only the
    /// EXIT half of the rule sees it. Refused (`last` into the exit).
    RotatedLiveOut,
    /// `tmp = iv + iv; acc += tmp`: a temporary used only in its own iteration.
    /// Admitted with `[iv, acc]`.
    IterationTemporary,
    /// The exit reads the flags the loop's compare set. Refused.
    FlagsLiveOut,
    /// A call in the loop: register effects the model cannot enumerate.
    /// Refused.
    UnmodeledCall,
    // --- control: every way the loop can leave ---
    /// `if iv == stop { break }` to a block of its own. Refused: an exit the
    /// plan does not account for.
    BreakExit,
    /// The same `break` in the header, to the loop test's own exit block, so
    /// two transfers share the edge the plan names. Refused.
    HeaderBreakSameExit,
    /// A bounds check `iv <u N` (the loop's own bound) leaving to a trap
    /// block. Admitted: no iteration that passed the loop test fails it.
    GuardLoopBound,
    /// A bounds check against an unrelated length. Refused: it can fail in
    /// an iteration the new code replaces.
    GuardOtherBound,
    /// A bounds trap carrier `iv <u 64` (the loop's bound) in the body.
    /// Admitted.
    CarrierLoopBound,
    /// A bounds trap carrier `iv <u 32`. Refused.
    CarrierShortBound,
    /// The loop's bound carrier in the header, which runs once more than the
    /// body, with `iv == N`. Refused.
    CarrierInHeader,
    /// A check of `iv <u N` after the latch advanced `iv`: it fails on the
    /// last iteration. Refused.
    GuardAfterAdvance,
}

impl Row {
    /// The control rows, built on `IvOnly`.
    fn is_control(self) -> bool {
        matches!(
            self,
            Row::BreakExit
                | Row::HeaderBreakSameExit
                | Row::GuardLoopBound
                | Row::GuardOtherBound
                | Row::CarrierLoopBound
                | Row::CarrierShortBound
                | Row::CarrierInHeader
                | Row::GuardAfterAdvance
        )
    }
}

const ROWS: [Row; 18] = [
    Row::IvOnly,
    Row::IvAcc,
    Row::AccNotReproduced,
    Row::CountIfMerge,
    Row::SecondAccumulator,
    Row::LiveOutTemporary,
    Row::RotatedLiveOut,
    Row::IterationTemporary,
    Row::FlagsLiveOut,
    Row::UnmodeledCall,
    Row::BreakExit,
    Row::HeaderBreakSameExit,
    Row::GuardLoopBound,
    Row::GuardOtherBound,
    Row::CarrierLoopBound,
    Row::CarrierShortBound,
    Row::CarrierInHeader,
    Row::GuardAfterAdvance,
];

/// The expected verdict, independent of the IR's block type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Admitted,
    /// `reg` live into the loop header.
    LiveIntoHeader(StateReg),
    /// `reg` live into the (only) exit.
    LiveIntoExit(StateReg),
    Unmodeled,
    /// An exit the plan does not account for.
    UnaccountedExit,
}

fn gpr(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}

impl Row {
    fn carried(self) -> Vec<VReg> {
        match self {
            Row::IvOnly | Row::AccNotReproduced | Row::RotatedLiveOut => vec![gpr(IV)],
            row if row.is_control() => vec![gpr(IV)],
            _ => vec![gpr(IV), gpr(ACC)],
        }
    }

    fn expected(self) -> Verdict {
        match self {
            Row::IvOnly | Row::IvAcc | Row::CountIfMerge | Row::IterationTemporary => {
                Verdict::Admitted
            }
            Row::AccNotReproduced => Verdict::LiveIntoHeader(StateReg::Virtual(gpr(ACC))),
            Row::SecondAccumulator => Verdict::LiveIntoHeader(StateReg::Virtual(gpr(T))),
            Row::LiveOutTemporary => Verdict::LiveIntoHeader(StateReg::Virtual(gpr(LAST))),
            Row::RotatedLiveOut => Verdict::LiveIntoExit(StateReg::Virtual(gpr(LAST))),
            Row::FlagsLiveOut => Verdict::LiveIntoExit(StateReg::Flags),
            Row::UnmodeledCall => Verdict::Unmodeled,
            Row::GuardLoopBound | Row::CarrierLoopBound => Verdict::Admitted,
            Row::BreakExit
            | Row::HeaderBreakSameExit
            | Row::GuardOtherBound
            | Row::CarrierShortBound
            | Row::CarrierInHeader
            | Row::GuardAfterAdvance => Verdict::UnaccountedExit,
        }
    }
}

/// A built fixture: the function, the loop's blocks, its header and its exit.
struct Fixture<F, B> {
    func: F,
    blocks: Vec<B>,
    header: B,
    exit: B,
}

/// The plan every row's rewrite builds: the header's loop test, plus the
/// bounds checks the contract admits for an induction `iv <u N`.
fn plan<G: LoopStateView>(fixture: &Fixture<G, G::Block>) -> ExitPlan<G::Block> {
    ExitPlan::loop_test(fixture.header, fixture.exit).and_induction_guards(
        &fixture.func,
        fixture.blocks.iter().copied(),
        fixture.header,
        &InductionGuards {
            iv: gpr(IV),
            at_most_iv: &|v: VReg| v.id == IV,
            covers_loop_bound: &|bound| match bound {
                GuardBound::Imm(n) => n >= BOUND,
                GuardBound::Reg(r) => r.id == N,
            },
        },
    )
}

fn verdict<G: LoopStateView>(fixture: &Fixture<G, G::Block>, carried: &[VReg]) -> Verdict {
    match LoopLocality::check(
        &fixture.func,
        fixture.blocks.iter().copied(),
        fixture.header,
        &plan(fixture),
        Handoff::HeaderOrExit,
        carried,
    ) {
        Ok(_) => Verdict::Admitted,
        Err(LoopStateEscape::Live { reg, into }) if into == fixture.header => {
            Verdict::LiveIntoHeader(reg)
        }
        Err(LoopStateEscape::Live { reg, into }) => {
            assert_eq!(into, fixture.exit, "a live register escapes into the exit");
            Verdict::LiveIntoExit(reg)
        }
        Err(LoopStateEscape::Unmodeled { .. }) => Verdict::Unmodeled,
        Err(LoopStateEscape::Exit(_)) => Verdict::UnaccountedExit,
        Err(other) => panic!("unexpected escape {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// AArch64 fixtures
// ---------------------------------------------------------------------------

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(gpr(id))
}
fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}
fn blk(block: BlockId) -> MachOperand {
    MachOperand::Block(block)
}
const CC_EQ: i64 = 0;
const CC_LO: i64 = 3;

fn push(
    func: &mut MachFunction,
    block: BlockId,
    opcode: AArch64Opcode,
    operands: Vec<MachOperand>,
) {
    let id = func.push_inst(MachInst::new(opcode, operands));
    func.append_inst(block, id);
}

fn aarch64_fixture(row: Row) -> Fixture<MachFunction, BlockId> {
    use AArch64Opcode::*;
    let mut f = MachFunction::new(format!("{row:?}"), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    push(&mut f, entry, Movz, vec![x(N), imm(64)]);
    push(&mut f, entry, Movz, vec![x(IV), imm(0)]);
    push(&mut f, entry, Movz, vec![x(ACC), imm(0)]);
    push(&mut f, entry, Movz, vec![x(T), imm(0)]);
    push(&mut f, entry, Movz, vec![x(LAST), imm(0)]);
    push(&mut f, entry, B, vec![blk(header)]);
    f.add_edge(entry, header);

    if row == Row::RotatedLiveOut {
        // header == body == latch, bottom-tested.
        let exit = f.create_block();
        push(&mut f, header, MovR, vec![x(LAST), x(IV)]);
        push(&mut f, header, AddRI, vec![x(NEXT), x(IV), imm(1)]);
        push(&mut f, header, MovR, vec![x(IV), x(NEXT)]);
        push(&mut f, header, CmpRR, vec![x(IV), x(N)]);
        push(&mut f, header, BCond, vec![imm(CC_LO), blk(header)]);
        push(&mut f, header, B, vec![blk(exit)]);
        push(&mut f, exit, AddRR, vec![x(OUT), x(LAST), x(LAST)]);
        push(&mut f, exit, Ret, vec![]);
        f.add_edge(header, header);
        f.add_edge(header, exit);
        return Fixture {
            func: f,
            blocks: vec![header],
            header,
            exit,
        };
    }

    let body = f.create_block();
    let mut blocks = vec![header, body];
    // `latch` is where the induction advances; `body` unless a diamond splits it.
    let latch = if row == Row::CountIfMerge {
        let inc = f.create_block();
        let zero = f.create_block();
        let latch = f.create_block();
        push(&mut f, body, Cbz, vec![x(IV), blk(inc)]);
        push(&mut f, body, B, vec![blk(zero)]);
        push(&mut f, inc, AddRI, vec![x(MERGE), x(ACC), imm(1)]);
        push(&mut f, inc, B, vec![blk(latch)]);
        push(&mut f, zero, MovR, vec![x(MERGE), x(ACC)]);
        push(&mut f, zero, B, vec![blk(latch)]);
        push(&mut f, latch, MovR, vec![x(ACC), x(MERGE)]);
        f.add_edge(body, inc);
        f.add_edge(body, zero);
        f.add_edge(inc, latch);
        f.add_edge(zero, latch);
        blocks.extend([inc, zero, latch]);
        latch
    } else {
        match row {
            Row::IvAcc | Row::AccNotReproduced | Row::FlagsLiveOut => {
                push(&mut f, body, AddRR, vec![x(ACC), x(ACC), x(IV)]);
            }
            Row::SecondAccumulator => {
                push(&mut f, body, AddRR, vec![x(ACC), x(ACC), x(IV)]);
                push(&mut f, body, AddRR, vec![x(T), x(T), x(IV)]);
            }
            Row::LiveOutTemporary => {
                push(&mut f, body, AddRR, vec![x(ACC), x(ACC), x(IV)]);
                push(&mut f, body, MovR, vec![x(LAST), x(IV)]);
            }
            Row::IterationTemporary => {
                push(&mut f, body, AddRR, vec![x(TMP), x(IV), x(IV)]);
                push(&mut f, body, AddRR, vec![x(ACC), x(ACC), x(TMP)]);
            }
            Row::UnmodeledCall => {
                push(&mut f, body, Bl, vec![imm(0x1000)]);
                push(&mut f, body, AddRR, vec![x(ACC), x(ACC), x(IV)]);
            }
            Row::CarrierLoopBound => push(
                &mut f,
                body,
                TrapBoundsCheckExact,
                vec![x(BASE), x(IV), imm(BOUND)],
            ),
            Row::CarrierShortBound => push(
                &mut f,
                body,
                TrapBoundsCheckExact,
                vec![x(BASE), x(IV), imm(BOUND / 2)],
            ),
            _ => {}
        }
        body
    };
    push(&mut f, latch, AddRI, vec![x(NEXT), x(IV), imm(1)]);
    push(&mut f, latch, MovR, vec![x(IV), x(NEXT)]);

    let exit = f.create_block();
    // The control rows' extra blocks: a trap block, a `break` target, a
    // block in front of the body, a block after the latch's advance.
    let panic = f.create_block();
    push(&mut f, panic, Brk, vec![]);
    let brk = f.create_block();
    push(&mut f, brk, MovR, vec![x(OUT), x(IV)]);
    push(&mut f, brk, Ret, vec![]);
    let first = match row {
        Row::BreakExit | Row::GuardLoopBound | Row::GuardOtherBound => {
            let pre = f.create_block();
            blocks.push(pre);
            match row {
                Row::BreakExit => {
                    push(&mut f, pre, CmpRR, vec![x(IV), x(STOP)]);
                    push(&mut f, pre, BCond, vec![imm(CC_EQ), blk(brk)]);
                    push(&mut f, pre, B, vec![blk(body)]);
                    f.add_edge(pre, brk);
                }
                _ => {
                    let bound = if row == Row::GuardLoopBound { N } else { LEN };
                    push(&mut f, pre, CmpRR, vec![x(IV), x(bound)]);
                    push(&mut f, pre, BCond, vec![imm(CC_LO), blk(body)]);
                    push(&mut f, pre, B, vec![blk(panic)]);
                    f.add_edge(pre, panic);
                }
            }
            f.add_edge(pre, body);
            pre
        }
        _ => body,
    };
    if row == Row::GuardAfterAdvance {
        let post = f.create_block();
        blocks.push(post);
        push(&mut f, latch, B, vec![blk(post)]);
        f.add_edge(latch, post);
        push(&mut f, post, CmpRR, vec![x(IV), x(N)]);
        push(&mut f, post, BCond, vec![imm(CC_LO), blk(header)]);
        push(&mut f, post, B, vec![blk(panic)]);
        f.add_edge(post, header);
        f.add_edge(post, panic);
    } else {
        push(&mut f, latch, B, vec![blk(header)]);
        f.add_edge(latch, header);
    }

    match row {
        Row::CarrierInHeader => push(
            &mut f,
            header,
            TrapBoundsCheckExact,
            vec![x(BASE), x(IV), imm(BOUND)],
        ),
        Row::HeaderBreakSameExit => {
            push(&mut f, header, CmpRR, vec![x(IV), x(STOP)]);
            push(&mut f, header, BCond, vec![imm(CC_EQ), blk(exit)]);
        }
        _ => {}
    }
    push(&mut f, header, CmpRR, vec![x(IV), x(N)]);
    push(&mut f, header, BCond, vec![imm(CC_LO), blk(first)]);
    push(&mut f, header, B, vec![blk(exit)]);
    f.add_edge(header, first);
    f.add_edge(header, exit);
    match row {
        Row::LiveOutTemporary => push(&mut f, exit, AddRR, vec![x(OUT), x(ACC), x(LAST)]),
        Row::SecondAccumulator => push(&mut f, exit, AddRR, vec![x(OUT), x(ACC), x(T)]),
        Row::FlagsLiveOut => push(&mut f, exit, CSet, vec![x(OUT), imm(CC_LO)]),
        row if row == Row::IvOnly || row.is_control() => {
            push(&mut f, exit, MovR, vec![x(OUT), x(IV)])
        }
        _ => push(&mut f, exit, MovR, vec![x(OUT), x(ACC)]),
    }
    push(&mut f, exit, Ret, vec![]);
    Fixture {
        func: f,
        blocks,
        header,
        exit,
    }
}

// ---------------------------------------------------------------------------
// x86-64 fixtures (the same rows in the x86 selector's dialect: tied
// two-operand ALU forms, `Jcc` + `Jmp` terminators, successor lists)
// ---------------------------------------------------------------------------

fn xv(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(gpr(id))
}
fn xi(value: i64) -> X86ISelOperand {
    X86ISelOperand::Imm(value)
}
fn xb(block: Block) -> X86ISelOperand {
    X86ISelOperand::Block(block)
}

fn xpush(
    func: &mut X86ISelFunction,
    block: Block,
    opcode: X86Opcode,
    operands: Vec<X86ISelOperand>,
) {
    func.push_inst(block, X86ISelInst::new(opcode, operands));
}

fn jcc(cc: X86CondCode, target: Block) -> Vec<X86ISelOperand> {
    vec![X86ISelOperand::CondCode(cc), xb(target)]
}

fn x86_fixture(row: Row) -> Fixture<X86ISelFunction, Block> {
    use X86Opcode::*;
    let mut f = X86ISelFunction::new(
        format!("{row:?}"),
        X86Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let entry = Block(0);
    let header = Block(1);
    let body = Block(2);
    let inc = Block(3);
    let zero = Block(4);
    let latch_block = Block(5);
    let exit = Block(6);
    let pre = Block(7);
    let panic = Block(8);
    let brk = Block(9);
    let post = Block(10);
    for block in [entry, header, body, inc, zero, latch_block, exit] {
        f.ensure_block(block);
    }
    xpush(&mut f, entry, MovRI, vec![xv(N), xi(64)]);
    xpush(&mut f, entry, MovRI, vec![xv(IV), xi(0)]);
    xpush(&mut f, entry, MovRI, vec![xv(ACC), xi(0)]);
    xpush(&mut f, entry, MovRI, vec![xv(T), xi(0)]);
    xpush(&mut f, entry, MovRI, vec![xv(LAST), xi(0)]);
    xpush(&mut f, entry, Jmp, vec![xb(header)]);
    f.add_successor(entry, header);

    if row == Row::RotatedLiveOut {
        xpush(&mut f, header, MovRR, vec![xv(LAST), xv(IV)]);
        xpush(&mut f, header, MovRR, vec![xv(NEXT), xv(IV)]);
        xpush(&mut f, header, AddRI, vec![xv(NEXT), xi(1)]);
        xpush(&mut f, header, MovRR, vec![xv(IV), xv(NEXT)]);
        xpush(&mut f, header, CmpRR, vec![xv(IV), xv(N)]);
        xpush(&mut f, header, Jcc, jcc(X86CondCode::B, header));
        xpush(&mut f, header, Jmp, vec![xb(exit)]);
        f.add_successor(header, header);
        f.add_successor(header, exit);
        xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(LAST)]);
        xpush(&mut f, exit, Ret, vec![]);
        return Fixture {
            func: f,
            blocks: vec![header],
            header,
            exit,
        };
    }

    let mut blocks = vec![header, body];
    let latch = if row == Row::CountIfMerge {
        xpush(&mut f, body, TestRR, vec![xv(IV), xv(IV)]);
        xpush(&mut f, body, Jcc, jcc(X86CondCode::E, inc));
        xpush(&mut f, body, Jmp, vec![xb(zero)]);
        xpush(&mut f, inc, MovRR, vec![xv(MERGE), xv(ACC)]);
        xpush(&mut f, inc, AddRI, vec![xv(MERGE), xi(1)]);
        xpush(&mut f, inc, Jmp, vec![xb(latch_block)]);
        xpush(&mut f, zero, MovRR, vec![xv(MERGE), xv(ACC)]);
        xpush(&mut f, zero, Jmp, vec![xb(latch_block)]);
        xpush(&mut f, latch_block, MovRR, vec![xv(ACC), xv(MERGE)]);
        f.add_successor(body, inc);
        f.add_successor(body, zero);
        f.add_successor(inc, latch_block);
        f.add_successor(zero, latch_block);
        blocks.extend([inc, zero, latch_block]);
        latch_block
    } else {
        match row {
            Row::IvAcc | Row::AccNotReproduced | Row::FlagsLiveOut => {
                xpush(&mut f, body, AddRR, vec![xv(ACC), xv(IV)]);
            }
            Row::SecondAccumulator => {
                xpush(&mut f, body, AddRR, vec![xv(ACC), xv(IV)]);
                xpush(&mut f, body, AddRR, vec![xv(T), xv(IV)]);
            }
            Row::LiveOutTemporary => {
                xpush(&mut f, body, AddRR, vec![xv(ACC), xv(IV)]);
                xpush(&mut f, body, MovRR, vec![xv(LAST), xv(IV)]);
            }
            Row::IterationTemporary => {
                xpush(&mut f, body, MovRR, vec![xv(TMP), xv(IV)]);
                xpush(&mut f, body, AddRR, vec![xv(TMP), xv(IV)]);
                xpush(&mut f, body, AddRR, vec![xv(ACC), xv(TMP)]);
            }
            Row::UnmodeledCall => {
                xpush(
                    &mut f,
                    body,
                    Call,
                    vec![X86ISelOperand::Symbol("callee".to_string())],
                );
                xpush(&mut f, body, AddRR, vec![xv(ACC), xv(IV)]);
            }
            Row::CarrierLoopBound => xpush(
                &mut f,
                body,
                TrapBoundsCheckExact,
                vec![xv(BASE), xv(IV), xi(BOUND)],
            ),
            Row::CarrierShortBound => xpush(
                &mut f,
                body,
                TrapBoundsCheckExact,
                vec![xv(BASE), xv(IV), xi(BOUND / 2)],
            ),
            _ => {}
        }
        body
    };
    xpush(&mut f, latch, MovRR, vec![xv(NEXT), xv(IV)]);
    xpush(&mut f, latch, AddRI, vec![xv(NEXT), xi(1)]);
    xpush(&mut f, latch, MovRR, vec![xv(IV), xv(NEXT)]);

    // The control rows' extra blocks (see `aarch64_fixture`).
    for block in [pre, panic, brk, post] {
        f.ensure_block(block);
    }
    xpush(&mut f, panic, Ud2, vec![]);
    xpush(&mut f, brk, MovRR, vec![xv(OUT), xv(IV)]);
    xpush(&mut f, brk, Ret, vec![]);
    let first = match row {
        Row::BreakExit => {
            xpush(&mut f, pre, CmpRR, vec![xv(IV), xv(STOP)]);
            xpush(&mut f, pre, Jcc, jcc(X86CondCode::E, brk));
            xpush(&mut f, pre, Jmp, vec![xb(body)]);
            f.add_successor(pre, brk);
            f.add_successor(pre, body);
            blocks.push(pre);
            pre
        }
        Row::GuardLoopBound | Row::GuardOtherBound => {
            let bound = if row == Row::GuardLoopBound { N } else { LEN };
            xpush(&mut f, pre, CmpRR, vec![xv(IV), xv(bound)]);
            xpush(&mut f, pre, Jcc, jcc(X86CondCode::AE, panic));
            xpush(&mut f, pre, Jmp, vec![xb(body)]);
            f.add_successor(pre, panic);
            f.add_successor(pre, body);
            blocks.push(pre);
            pre
        }
        _ => body,
    };
    if row == Row::GuardAfterAdvance {
        xpush(&mut f, latch, Jmp, vec![xb(post)]);
        f.add_successor(latch, post);
        xpush(&mut f, post, CmpRR, vec![xv(IV), xv(N)]);
        xpush(&mut f, post, Jcc, jcc(X86CondCode::B, header));
        xpush(&mut f, post, Jmp, vec![xb(panic)]);
        f.add_successor(post, header);
        f.add_successor(post, panic);
        blocks.push(post);
    } else {
        xpush(&mut f, latch, Jmp, vec![xb(header)]);
        f.add_successor(latch, header);
    }

    match row {
        Row::CarrierInHeader => xpush(
            &mut f,
            header,
            TrapBoundsCheckExact,
            vec![xv(BASE), xv(IV), xi(BOUND)],
        ),
        Row::HeaderBreakSameExit => {
            xpush(&mut f, header, CmpRR, vec![xv(IV), xv(STOP)]);
            xpush(&mut f, header, Jcc, jcc(X86CondCode::E, exit));
        }
        _ => {}
    }
    xpush(&mut f, header, CmpRR, vec![xv(IV), xv(N)]);
    xpush(&mut f, header, Jcc, jcc(X86CondCode::B, first));
    xpush(&mut f, header, Jmp, vec![xb(exit)]);
    f.add_successor(header, first);
    f.add_successor(header, exit);
    match row {
        Row::LiveOutTemporary => {
            xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(ACC)]);
            xpush(&mut f, exit, AddRR, vec![xv(OUT), xv(LAST)]);
        }
        Row::SecondAccumulator => {
            xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(ACC)]);
            xpush(&mut f, exit, AddRR, vec![xv(OUT), xv(T)]);
        }
        Row::FlagsLiveOut => {
            xpush(
                &mut f,
                exit,
                Setcc,
                vec![xv(OUT), X86ISelOperand::CondCode(X86CondCode::B)],
            );
        }
        row if row == Row::IvOnly || row.is_control() => {
            xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(IV)])
        }
        _ => xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(ACC)]),
    }
    xpush(&mut f, exit, Ret, vec![]);
    Fixture {
        func: f,
        blocks,
        header,
        exit,
    }
}

/// The table: every row over both IRs gives the same verdict, and that verdict
/// is the expected one.
#[test]
fn loop_locality_table() {
    for row in ROWS {
        let carried = row.carried();
        let aarch64 = verdict(&aarch64_fixture(row), &carried);
        let x86 = verdict(&x86_fixture(row), &carried);
        assert_eq!(aarch64, row.expected(), "aarch64 row {row:?}");
        assert_eq!(x86, row.expected(), "x86-64 row {row:?}");
    }
}

/// The exit half is load-bearing on its own. In the rotated row the header
/// half alone admits the loop, since `last` is written on entry to the header
/// before any read. Only the check at the exit refuses it. This is the shape
/// of the measured aarch64 `last = i` miscompile when the scalar remainder is
/// empty and the rewrite hands off straight to the exit.
#[test]
fn rotated_live_out_is_refused_only_by_the_exit_half() {
    let carried = Row::RotatedLiveOut.carried();
    let a64 = aarch64_fixture(Row::RotatedLiveOut);
    let walker = Walker::new(&a64.func);
    assert!(
        !walker.live_into(a64.header, StateReg::Virtual(gpr(LAST))),
        "the header half alone must not see `last`"
    );
    assert!(walker.live_into(a64.exit, StateReg::Virtual(gpr(LAST))));
    assert_eq!(
        verdict(&a64, &carried),
        Verdict::LiveIntoExit(StateReg::Virtual(gpr(LAST)))
    );
    let x86 = x86_fixture(Row::RotatedLiveOut);
    let walker = Walker::new(&x86.func);
    assert!(!walker.live_into(x86.header, StateReg::Virtual(gpr(LAST))));
    assert!(walker.live_into(x86.exit, StateReg::Virtual(gpr(LAST))));
}

/// clang's rotated reduction: the test leaves from the end of the header,
/// and a latch of its own writes the loop's values back.
///
/// ```text
/// header: next = iv + 1; sum = acc + iv; if next == N goto exit; goto latch
/// latch:  iv = next; acc = sum; goto header
/// exit:   out = <read>
/// ```
fn rotated_aarch64_fixture(read: u32) -> Fixture<MachFunction, BlockId> {
    use AArch64Opcode::*;
    let mut f = MachFunction::new("rotated".to_string(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    push(&mut f, entry, Movz, vec![x(N), imm(BOUND)]);
    push(&mut f, entry, Movz, vec![x(IV), imm(0)]);
    push(&mut f, entry, Movz, vec![x(ACC), imm(0)]);
    push(&mut f, entry, B, vec![blk(header)]);
    push(&mut f, header, AddRI, vec![x(NEXT), x(IV), imm(1)]);
    push(&mut f, header, AddRR, vec![x(T), x(ACC), x(IV)]);
    push(&mut f, header, CmpRR, vec![x(NEXT), x(N)]);
    push(&mut f, header, BCond, vec![imm(CC_EQ), blk(exit)]);
    push(&mut f, header, B, vec![blk(latch)]);
    push(&mut f, latch, MovR, vec![x(IV), x(NEXT)]);
    push(&mut f, latch, MovR, vec![x(ACC), x(T)]);
    push(&mut f, latch, B, vec![blk(header)]);
    push(&mut f, exit, MovR, vec![x(OUT), x(read)]);
    push(&mut f, exit, Ret, vec![]);
    f.add_edge(entry, header);
    f.add_edge(header, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    Fixture {
        func: f,
        blocks: vec![header, latch],
        header,
        exit,
    }
}

/// [`rotated_aarch64_fixture`] in the x86 selector's dialect.
fn rotated_x86_fixture(read: u32) -> Fixture<X86ISelFunction, Block> {
    use X86Opcode::*;
    let mut f = X86ISelFunction::new(
        "rotated".to_string(),
        X86Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let (entry, header, latch, exit) = (Block(0), Block(1), Block(2), Block(3));
    for block in [entry, header, latch, exit] {
        f.ensure_block(block);
    }
    xpush(&mut f, entry, MovRI, vec![xv(N), xi(BOUND)]);
    xpush(&mut f, entry, MovRI, vec![xv(IV), xi(0)]);
    xpush(&mut f, entry, MovRI, vec![xv(ACC), xi(0)]);
    xpush(&mut f, entry, Jmp, vec![xb(header)]);
    f.add_successor(entry, header);
    xpush(&mut f, header, MovRR, vec![xv(NEXT), xv(IV)]);
    xpush(&mut f, header, AddRI, vec![xv(NEXT), xi(1)]);
    xpush(&mut f, header, MovRR, vec![xv(T), xv(ACC)]);
    xpush(&mut f, header, AddRR, vec![xv(T), xv(IV)]);
    xpush(&mut f, header, CmpRR, vec![xv(NEXT), xv(N)]);
    xpush(&mut f, header, Jcc, jcc(X86CondCode::E, exit));
    xpush(&mut f, header, Jmp, vec![xb(latch)]);
    f.add_successor(header, exit);
    f.add_successor(header, latch);
    xpush(&mut f, latch, MovRR, vec![xv(IV), xv(NEXT)]);
    xpush(&mut f, latch, MovRR, vec![xv(ACC), xv(T)]);
    xpush(&mut f, latch, Jmp, vec![xb(header)]);
    f.add_successor(latch, header);
    xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(read)]);
    xpush(&mut f, exit, Ret, vec![]);
    Fixture {
        func: f,
        blocks: vec![header, latch],
        header,
        exit,
    }
}

/// A rotated rewrite that also leaves straight to the exit, reproducing `iv`,
/// `acc` and `sum` (the `neon_array` set).
fn check_rotated_fixture<G: LoopStateView>(
    fixture: &Fixture<G, G::Block>,
    carried: &[VReg],
) -> Result<(), LoopStateEscape<G::Block>> {
    LoopLocality::check_rotated(
        &fixture.func,
        fixture.blocks.iter().copied(),
        fixture.header,
        &ExitPlan::loop_test(fixture.header, fixture.exit),
        carried,
    )
    .map(|_| ())
}

/// The same rewrite under [`LoopLocality::check`], which treats `carried` as
/// reproduced at the exit too.
fn check_fixture<G: LoopStateView>(
    fixture: &Fixture<G, G::Block>,
    carried: &[VReg],
) -> Result<(), LoopStateEscape<G::Block>> {
    LoopLocality::check(
        &fixture.func,
        fixture.blocks.iter().copied(),
        fixture.header,
        &ExitPlan::loop_test(fixture.header, fixture.exit),
        Handoff::HeaderOrExit,
        carried,
    )
    .map(|_| ())
}

/// At a rotated loop's exit the contract itself finds the carried registers
/// the latch writes back after the test, and refuses an exit that reads one.
/// The rewrite reproduces `iv`, `acc` and `sum`, the state the loop carries
/// into its next iteration. Leaving through its test, the loop holds `iv`
/// and `acc` from before the latch, so an exit reading either is refused;
/// `sum` is written before the test and stays reproduced. `check` admits all
/// three, so the refusals come from the rotated check alone. Both IRs.
#[test]
fn a_rotated_exit_sees_the_registers_its_latch_writes_back() {
    let carried = [gpr(IV), gpr(ACC), gpr(T)];
    for (read, stale) in [(T, false), (ACC, true), (IV, true)] {
        let live = StateReg::Virtual(gpr(read));
        let a64 = rotated_aarch64_fixture(read);
        assert_eq!(check_fixture(&a64, &carried), Ok(()), "aarch64 {read}");
        let want = if stale {
            Err(LoopStateEscape::Live {
                reg: live,
                into: a64.exit,
            })
        } else {
            Ok(())
        };
        assert_eq!(
            check_rotated_fixture(&a64, &carried),
            want,
            "aarch64 {read}"
        );
        let x86 = rotated_x86_fixture(read);
        assert_eq!(check_fixture(&x86, &carried), Ok(()), "x86 {read}");
        let want = if stale {
            Err(LoopStateEscape::Live {
                reg: live,
                into: x86.exit,
            })
        } else {
            Ok(())
        };
        assert_eq!(check_rotated_fixture(&x86, &carried), want, "x86 {read}");
    }
}

/// A bottom-tested loop writes nothing after its test: the rotated row's
/// header computes `last`, steps `iv` and then leaves, so the rotated check
/// treats both as reproduced at the exit, as `check` does.
#[test]
fn a_bottom_tested_exit_holds_every_carried_register() {
    let carried = [gpr(IV), gpr(LAST)];
    let a64 = aarch64_fixture(Row::RotatedLiveOut);
    assert_eq!(check_rotated_fixture(&a64, &carried), Ok(()));
    let x86 = x86_fixture(Row::RotatedLiveOut);
    assert_eq!(check_rotated_fixture(&x86, &carried), Ok(()));
}

/// A read of a narrower view of a tracked register observes it: `w16` reads
/// `x16`'s low half.
#[test]
fn a_narrower_view_is_a_read() {
    let mut f = aarch64_fixture(Row::IvAcc);
    let exit = f.exit;
    let first = f.func.block(exit).insts[0];
    f.func.inst_mut(first).operands[1] = MachOperand::VReg(VReg::new(ACC, RegClass::Gpr32));
    // The exit now reads `w11`; `acc` is still carried, so admitted.
    assert_eq!(verdict(&f, &Row::IvAcc.carried()), Verdict::Admitted);
    // Not reproduced: the narrow read is a read of `x11`.
    assert_eq!(
        verdict(&f, &[gpr(IV)]),
        Verdict::LiveIntoHeader(StateReg::Virtual(gpr(ACC)))
    );
}

/// A physical register operand in the loop is refused, not guessed at.
#[test]
fn a_physical_register_operand_is_unmodeled() {
    let mut f = aarch64_fixture(Row::IvAcc);
    let body = f.blocks[1];
    let id = f.func.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X0), x(IV)],
    ));
    f.func.block_mut(body).insts.insert(0, id);
    assert_eq!(verdict(&f, &Row::IvAcc.carried()), Verdict::Unmodeled);
}

/// `Handoff::Header` checks only the header: it admits a header-computed value
/// read at the exit (the header recomputes it after any hand-off), and it
/// still refuses every register live into the header. Under
/// `Handoff::HeaderOrExit` the same header value is refused.
#[test]
fn header_handoff_checks_only_the_header() {
    use AArch64Opcode::*;
    // IvAcc, plus `z = 0` materialized in the header and read at the exit.
    let mut f = aarch64_fixture(Row::IvAcc);
    let header = f.header;
    let exit = f.exit;
    let id = f.func.push_inst(MachInst::new(Movz, vec![x(T), imm(0)]));
    f.func.block_mut(header).insts.insert(0, id);
    let id = f.func.push_inst(MachInst::new(MovR, vec![x(OUT), x(T)]));
    f.func.block_mut(exit).insts.insert(0, id);
    let check = |handoff, carried: &[VReg]| {
        LoopLocality::check(
            &f.func,
            f.blocks.iter().copied(),
            header,
            &plan(&f),
            handoff,
            carried,
        )
    };
    let carried = Row::IvAcc.carried();
    assert!(check(Handoff::Header, &carried).is_ok());
    assert_eq!(
        check(Handoff::HeaderOrExit, &carried),
        Err(LoopStateEscape::Live {
            reg: StateReg::Virtual(gpr(T)),
            into: exit
        })
    );
    // The header half still applies: `acc` not reproduced.
    assert!(check(Handoff::Header, &[gpr(IV)]).is_err());
    // The rotated live-out row is exactly what `Header` would miss, so a
    // rotated rewrite must never claim it.
    let rotated = aarch64_fixture(Row::RotatedLiveOut);
    assert!(
        LoopLocality::check(
            &rotated.func,
            rotated.blocks.iter().copied(),
            rotated.header,
            &plan(&rotated),
            Handoff::Header,
            &Row::RotatedLiveOut.carried(),
        )
        .is_ok()
    );
}

// ---------------------------------------------------------------------------
// Control: the exit plan
// ---------------------------------------------------------------------------

/// The control rows' exits are enumerated by the contract, not the pass: the
/// `break` row has exactly the loop test and the `break` edge.
#[test]
fn the_contract_enumerates_every_way_the_loop_leaves() {
    let a64 = aarch64_fixture(Row::BreakExit);
    let exits: Vec<LoopExit<BlockId>> = loop_exits(&a64.func, a64.blocks.iter().copied())
        .into_iter()
        .map(|(exit, transfers)| {
            assert_eq!(transfers, 1);
            exit
        })
        .collect();
    assert_eq!(exits.len(), 2, "{exits:?}");
    assert!(exits.contains(&LoopExit::Edge {
        from: a64.header,
        to: a64.exit
    }));
    // A carrier is a way out with no CFG edge.
    let carrier = aarch64_fixture(Row::CarrierLoopBound);
    assert!(
        loop_exits(&carrier.func, carrier.blocks.iter().copied())
            .iter()
            .any(|(exit, _)| matches!(exit, LoopExit::Stop { .. }))
    );
}

/// A pass that reproduces the `break` (an early-exit search) names it, and the
/// loop is admitted; the same plan without the claim is refused.
#[test]
fn a_reproduced_exit_is_admitted_only_when_claimed() {
    let f = aarch64_fixture(Row::BreakExit);
    let brk = loop_exits(&f.func, f.blocks.iter().copied())
        .into_iter()
        .map(|(exit, _)| exit)
        .find(|exit| {
            *exit
                != LoopExit::Edge {
                    from: f.header,
                    to: f.exit,
                }
        })
        .expect("the break edge");
    let check = |exits: &ExitPlan<BlockId>| {
        LoopLocality::check(
            &f.func,
            f.blocks.iter().copied(),
            f.header,
            exits,
            Handoff::HeaderOrExit,
            &[gpr(IV)],
        )
    };
    assert_eq!(
        check(&ExitPlan::loop_test(f.header, f.exit)),
        Err(LoopStateEscape::Exit(brk))
    );
    assert!(check(&ExitPlan::loop_test(f.header, f.exit).and_reproduces(brk)).is_ok());
}

/// A plan that names an edge the loop does not leave by is malformed.
#[test]
fn a_claim_that_is_not_an_exit_is_refused() {
    let f = aarch64_fixture(Row::IvOnly);
    let body = f.blocks[1];
    let wrong = LoopExit::Edge {
        from: body,
        to: f.header,
    };
    assert_eq!(
        LoopLocality::check(
            &f.func,
            f.blocks.iter().copied(),
            f.header,
            &ExitPlan::loop_test(f.header, f.exit).and_proved_not_taken(wrong),
            Handoff::HeaderOrExit,
            &[gpr(IV)],
        ),
        Err(LoopStateEscape::NotAnExit(wrong))
    );
}

/// `exit_of_test` names the test block's exit only when it has exactly one.
#[test]
fn exit_of_test_needs_a_single_exit() {
    let f = aarch64_fixture(Row::IvOnly);
    assert_eq!(
        exit_of_test(&f.func, f.blocks.iter().copied(), f.header),
        Some(f.exit)
    );
    let body = f.blocks[1];
    assert_eq!(exit_of_test(&f.func, f.blocks.iter().copied(), body), None);
    // The `break` row's `pre` block leaves to the break target alone.
    let brk = aarch64_fixture(Row::BreakExit);
    let pre = *brk.blocks.last().expect("pre block");
    assert!(exit_of_test(&brk.func, brk.blocks.iter().copied(), pre).is_some());
}

/// x86's raw-isel bounds check: `cmp iv, bound; setb s; movzx; movzx; and 1;
/// cmp s, 0; jne in; jmp trap`. The contract reads the materialized boolean
/// back to the compare: admitted against the loop's bound, refused against
/// another length, and refused when nothing clears the bits `setb` leaves.
#[test]
fn x86_setcc_bounds_diamond_is_a_guard() {
    use X86Opcode::*;
    const S32: u32 = 30;
    const S64: u32 = 31;
    let build = |bound: u32, normalize: bool| {
        let mut f = x86_fixture(Row::IvOnly);
        let header = f.header;
        let body = f.blocks[1];
        let pre = Block(11);
        let trap = Block(12);
        f.func.ensure_block(pre);
        f.func.ensure_block(trap);
        xpush(&mut f.func, trap, Ud2, vec![]);
        let s32 = X86ISelOperand::VReg(VReg::new(S32, RegClass::Gpr32));
        let s64 = X86ISelOperand::VReg(VReg::new(S64, RegClass::Gpr64));
        xpush(&mut f.func, pre, CmpRR, vec![xv(IV), xv(bound)]);
        xpush(
            &mut f.func,
            pre,
            Setcc,
            vec![s32.clone(), X86ISelOperand::CondCode(X86CondCode::B)],
        );
        if normalize {
            xpush(&mut f.func, pre, Movzx, vec![s32.clone(), s32.clone()]);
            xpush(&mut f.func, pre, Movzx, vec![s64.clone(), s32.clone()]);
            xpush(
                &mut f.func,
                pre,
                AndRI,
                vec![s64.clone(), s64.clone(), xi(1)],
            );
        } else {
            xpush(&mut f.func, pre, MovRR, vec![s64.clone(), s32.clone()]);
        }
        xpush(&mut f.func, pre, CmpRI, vec![s64, xi(0)]);
        xpush(&mut f.func, pre, Jcc, jcc(X86CondCode::NE, body));
        xpush(&mut f.func, pre, Jmp, vec![xb(trap)]);
        f.func.add_successor(pre, body);
        f.func.add_successor(pre, trap);
        // The header's continue edge now enters `pre`.
        let insts = &mut f.func.blocks.get_mut(&header).expect("header").insts;
        let jcc_at = insts
            .iter()
            .position(|inst| inst.opcode == Jcc)
            .expect("header jcc");
        insts[jcc_at] = X86ISelInst::new(Jcc, jcc(X86CondCode::B, pre));
        let successors = &mut f.func.blocks.get_mut(&header).expect("header").successors;
        successors.retain(|&s| s != body);
        successors.push(pre);
        f.blocks.push(pre);
        verdict(&f, &[gpr(IV)])
    };
    assert_eq!(build(N, true), Verdict::Admitted);
    assert_eq!(build(LEN, true), Verdict::UnaccountedExit);
    assert_eq!(build(N, false), Verdict::UnaccountedExit);
}

/// Every register a fixture's instructions name, in each class they use, plus
/// the flags and an unused number.
fn state_regs_of(func: &MachFunction) -> Vec<StateReg> {
    let mut regs: Vec<StateReg> = vec![StateReg::Flags, StateReg::Virtual(gpr(99))];
    for &block in &func.block_order {
        for index in 0..func.block(block).insts.len() {
            let mut note = |reg: StateReg| {
                if !regs.contains(&reg) {
                    regs.push(reg);
                }
            };
            func.visit_state_reads(block, index, &mut |reg| note(reg));
            func.visit_state_writes(block, index, &mut |reg, _| note(reg));
        }
    }
    regs
}

/// The x86 counterpart of [`state_regs_of`].
fn x86_state_regs_of(func: &X86ISelFunction) -> Vec<StateReg> {
    let mut regs: Vec<StateReg> = vec![StateReg::Flags, StateReg::Virtual(gpr(99))];
    for block in func.layout_order() {
        for index in 0..func.inst_count(block) {
            let mut note = |reg: StateReg| {
                if !regs.contains(&reg) {
                    regs.push(reg);
                }
            };
            func.visit_state_reads(block, index, &mut |reg| note(reg));
            func.visit_state_writes(block, index, &mut |reg, _| note(reg));
        }
    }
    regs
}

/// Every (block, register) liveness answer of the whole-function index is the
/// literal forward walk's.
fn assert_index_matches_walks<G: LoopStateView>(ir: &G, regs: &[StateReg], what: &str) {
    let walker = Walker::new(ir);
    let index = LoopStateIndex::indexed_from_the_start(ir);
    for block in ir.layout_order() {
        for &reg in regs {
            assert_eq!(
                index.live_into(block, reg),
                walker.live_into(block, reg),
                "{what}: live_into({block:?}, {reg:?})"
            );
        }
    }
}

/// The amortized index answers what the walks answer, on every table row of
/// both IRs, and every row's verdict through an index that answers from the
/// whole-function facts from the start is the table's.
#[test]
fn an_amortized_index_answers_what_the_walks_answer() {
    for row in ROWS {
        let a64 = aarch64_fixture(row);
        assert_index_matches_walks(
            &a64.func,
            &state_regs_of(&a64.func),
            &format!("aarch64 {row:?}"),
        );
        let x86 = x86_fixture(row);
        assert_index_matches_walks(
            &x86.func,
            &x86_state_regs_of(&x86.func),
            &format!("x86 {row:?}"),
        );

        let carried = row.carried();
        let index = LoopStateIndex::indexed_from_the_start(&a64.func);
        let indexed_plan = ExitPlan::loop_test(a64.header, a64.exit).and_induction_guards_in(
            &index,
            a64.blocks.iter().copied(),
            a64.header,
            &InductionGuards {
                iv: gpr(IV),
                at_most_iv: &|v: VReg| v.id == IV,
                covers_loop_bound: &|bound| match bound {
                    GuardBound::Imm(n) => n >= BOUND,
                    GuardBound::Reg(r) => r.id == N,
                },
            },
        );
        assert_eq!(indexed_plan, plan(&a64), "aarch64 {row:?}: plan");
        let indexed = LoopLocality::check_in(
            &index,
            a64.blocks.iter().copied(),
            a64.header,
            &indexed_plan,
            Handoff::HeaderOrExit,
            &carried,
        )
        .err();
        let literal = LoopLocality::check(
            &a64.func,
            a64.blocks.iter().copied(),
            a64.header,
            &plan(&a64),
            Handoff::HeaderOrExit,
            &carried,
        )
        .err();
        assert_eq!(indexed, literal, "aarch64 {row:?}: verdict");
    }
}

/// A deterministic generator of AArch64 machine functions with arbitrary
/// control flow: conditional and unconditional branches, fall-throughs,
/// returns, CFG edges a branch does not name and branches the CFG does not
/// list, self-loops, unreachable blocks, flag writers and readers, and reads
/// of a register's 32-bit view.
fn generated_function(seed: u64) -> MachFunction {
    use AArch64Opcode::*;
    let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    let mut next = move |bound: u64| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % bound
    };
    let mut f = MachFunction::new(format!("gen{seed}"), Signature::new(vec![], vec![]));
    let n = 2 + next(14) as u32;
    let mut blocks = vec![f.entry];
    for _ in 1..n {
        blocks.push(f.create_block());
    }
    let reg = |id: u64| gpr(1 + id as u32);
    let w = |id: u64| MachOperand::VReg(VReg::new(1 + id as u32, RegClass::Gpr32));
    for (position, &block) in blocks.iter().enumerate() {
        for _ in 0..next(4) {
            match next(6) {
                0 => push(
                    &mut f,
                    block,
                    Movz,
                    vec![MachOperand::VReg(reg(next(6))), imm(1)],
                ),
                1 => push(
                    &mut f,
                    block,
                    AddRR,
                    vec![
                        MachOperand::VReg(reg(next(6))),
                        MachOperand::VReg(reg(next(6))),
                        MachOperand::VReg(reg(next(6))),
                    ],
                ),
                2 => push(
                    &mut f,
                    block,
                    CmpRR,
                    vec![
                        MachOperand::VReg(reg(next(6))),
                        MachOperand::VReg(reg(next(6))),
                    ],
                ),
                3 => push(
                    &mut f,
                    block,
                    MovR,
                    vec![
                        MachOperand::VReg(reg(next(6))),
                        MachOperand::VReg(reg(next(6))),
                    ],
                ),
                4 => push(
                    &mut f,
                    block,
                    AddRR,
                    vec![w(next(6)), w(next(6)), w(next(6))],
                ),
                _ => push(&mut f, block, CSet, vec![w(next(6)), imm(CC_EQ)]),
            }
        }
        let target = blocks[next(u64::from(n)) as usize];
        let other = blocks[next(u64::from(n)) as usize];
        let fall = blocks.get(position + 1).copied();
        match next(6) {
            0 => {
                push(&mut f, block, B, vec![blk(target)]);
                if next(5) != 0 {
                    f.add_edge(block, target);
                }
            }
            1 => {
                push(&mut f, block, BCond, vec![imm(CC_LO), blk(target)]);
                push(&mut f, block, B, vec![blk(other)]);
                f.add_edge(block, target);
                f.add_edge(block, other);
            }
            2 => {
                // Conditional branch that falls through.
                push(&mut f, block, BCond, vec![imm(CC_EQ), blk(target)]);
                f.add_edge(block, target);
                if let Some(fall) = fall {
                    f.add_edge(block, fall);
                }
            }
            3 => push(&mut f, block, Ret, vec![]),
            4 => {
                // An edge only the CFG names.
                if next(2) == 0 {
                    f.add_edge(block, other);
                }
            }
            _ => {
                push(
                    &mut f,
                    block,
                    Cbz,
                    vec![MachOperand::VReg(reg(next(6))), blk(target)],
                );
                push(&mut f, block, B, vec![blk(other)]);
                f.add_edge(block, target);
                f.add_edge(block, other);
            }
        }
    }
    // Permute the layout after the entry.
    for i in (2..f.block_order.len()).rev() {
        let j = 1 + next(i as u64) as usize;
        f.block_order.swap(i, j);
    }
    f
}

/// The whole-function index answers every (block, register) question the
/// literal walk answers, on 400 generated functions.
#[test]
fn an_amortized_index_answers_what_the_walks_answer_on_generated_functions() {
    for seed in 0..400u64 {
        let f = generated_function(seed);
        assert_index_matches_walks(&f, &state_regs_of(&f), &format!("seed {seed}"));
    }
}

/// An amortized index answers with literal walks until they have visited as
/// many blocks as the function has, then from the whole-function index.
#[test]
fn an_amortized_index_switches_only_after_the_walks_paid_for_it() {
    let f = generated_function(7);
    let index = LoopStateIndex::amortized(&f);
    assert!(index.liveness.get().is_none());
    let reg = StateReg::Virtual(gpr(99));
    // An unread register: each walk visits every block reachable from its start.
    let mut asked = 0;
    while index.liveness.get().is_none() && asked < 64 {
        for block in f.layout_order() {
            assert!(!index.live_into(block, reg));
            asked += 1;
        }
    }
    assert!(
        index.liveness.get().is_some(),
        "the walks never paid for the index"
    );
    assert!(index.walked.get() >= index.layout_blocks);
    let literal = LoopStateIndex::literal(&f);
    for block in f.layout_order() {
        assert!(!literal.live_into(block, reg));
    }
    assert!(
        literal.liveness.get().is_none(),
        "a literal index never builds one"
    );
}

// ---- a proven-dead guard target that READS a register -------------------
//
// The shape upstream `c876e3bd0` made the native default: a failed bounds
// check is lowered to a faithful `panic_bounds_check` raise, and
// `assert_panic::emit` marshals `index`/`len` INTO that block. So the guard's
// failure target READS a copy of the IV, where the older `[Ud2]` trap read
// nothing.
//
// `ExitPlan::accounts_for` already treats the guard edge as settled for the
// CONTROL check. These pin that the REGISTER check now agrees — and, first,
// that it still refuses both shapes where agreeing would be unsound.

/// `header -> guard -> {latch, raise}`, where `raise` reads `iv`.
/// `shared` also gives `raise` a predecessor OUTSIDE the loop; `bound` is the
/// register the guard compares against (`N` is the loop's own bound, `LEN` an
/// unrelated length the plan cannot prove).
fn x86_raise_guard_fixture(bound: u32, shared: bool) -> Fixture<X86ISelFunction, Block> {
    use X86Opcode::*;
    let mut f = X86ISelFunction::new(
        format!("raise_guard_{bound}_{shared}"),
        X86Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let entry = Block(0);
    let header = Block(1);
    let guard = Block(2);
    let latch = Block(3);
    let exit = Block(4);
    let raise = Block(5);
    for block in [entry, header, guard, latch, exit, raise] {
        f.ensure_block(block);
    }

    xpush(&mut f, entry, MovRI, vec![xv(N), xi(BOUND)]);
    xpush(&mut f, entry, MovRI, vec![xv(LEN), xi(BOUND - 1)]);
    xpush(&mut f, entry, MovRI, vec![xv(IV), xi(0)]);
    if shared {
        // An outside predecessor keeps `raise` live no matter what this loop's
        // plan proves, so the liveness answer there describes a path the plan
        // says nothing about.
        xpush(&mut f, entry, TestRR, vec![xv(IV), xv(IV)]);
        xpush(&mut f, entry, Jcc, jcc(X86CondCode::E, raise));
        f.add_successor(entry, raise);
    }
    xpush(&mut f, entry, Jmp, vec![xb(header)]);
    f.add_successor(entry, header);

    xpush(&mut f, header, CmpRR, vec![xv(IV), xv(N)]);
    xpush(&mut f, header, Jcc, jcc(X86CondCode::B, guard));
    xpush(&mut f, header, Jmp, vec![xb(exit)]);
    f.add_successor(header, guard);
    f.add_successor(header, exit);

    // `TMP` is the real shape: a copy of the IV made INSIDE the loop, which
    // the rewrite does NOT reproduce, so the rule tracks it. v1_saxpy's v80 is
    // exactly this — `MovRR [v80, v72]` ahead of the bounds check — and it is
    // what the raise reads. Reading `IV` itself here would make these tests
    // vacuous: `IV` is in `carried`, hence "reproduced", hence never tracked.
    xpush(&mut f, guard, MovRR, vec![xv(TMP), xv(IV)]);
    xpush(&mut f, guard, CmpRR, vec![xv(TMP), xv(bound)]);
    xpush(&mut f, guard, Jcc, jcc(X86CondCode::B, latch));
    xpush(&mut f, guard, Jmp, vec![xb(raise)]);
    f.add_successor(guard, latch);
    f.add_successor(guard, raise);

    xpush(&mut f, latch, MovRR, vec![xv(NEXT), xv(IV)]);
    xpush(&mut f, latch, AddRI, vec![xv(NEXT), xi(1)]);
    xpush(&mut f, latch, MovRR, vec![xv(IV), xv(NEXT)]);
    xpush(&mut f, latch, Jmp, vec![xb(header)]);
    f.add_successor(latch, header);

    // The raise: it READS the induction variable, as the real one reads the
    // index it is about to report.
    xpush(&mut f, raise, MovRR, vec![xv(OUT), xv(TMP)]);
    xpush(&mut f, raise, Ret, vec![]);

    xpush(&mut f, exit, Ret, vec![]);

    Fixture {
        func: f,
        blocks: vec![header, guard, latch],
        header,
        exit,
    }
}

/// `plan()` admits only `v.id == IV` as at-most-iv; the guard here compares the
/// in-loop COPY, so these rows name it too. That is the same premise the x86
/// tier supplies through `prov(..) == Prov::Iv`.
fn raise_plan(fixture: &Fixture<X86ISelFunction, Block>) -> ExitPlan<Block> {
    ExitPlan::loop_test(fixture.header, fixture.exit).and_induction_guards(
        &fixture.func,
        fixture.blocks.iter().copied(),
        fixture.header,
        &InductionGuards {
            iv: gpr(IV),
            at_most_iv: &|v: VReg| v.id == IV || v.id == TMP,
            covers_loop_bound: &|bound| match bound {
                GuardBound::Imm(n) => n >= BOUND,
                GuardBound::Reg(r) => r.id == N,
            },
        },
    )
}

#[test]
fn a_raise_block_reached_only_by_a_proven_dead_guard_is_admitted() {
    // The guard is the loop's OWN bound, so no iteration the new code replaces
    // can fail it: `and_induction_guards` proves the edge untaken. The raise
    // reads `iv`, but nothing can reach it, so that read is unobservable.
    let fixture = x86_raise_guard_fixture(N, false);
    assert_eq!(
        LoopLocality::check(
            &fixture.func,
            fixture.blocks.iter().copied(),
            fixture.header,
            &raise_plan(&fixture),
            Handoff::HeaderOrExit,
            &[gpr(IV)],
        )
        .map(|_| ()),
        Ok(())
    );
}

#[test]
fn a_raise_block_with_a_predecessor_outside_the_loop_is_still_refused() {
    // Same proven-dead guard edge, but `entry` can also branch to the raise.
    // `live_into` is path-insensitive, so the block stays observable and the
    // loop must still be refused — on `iv`, into the raise block itself.
    let fixture = x86_raise_guard_fixture(N, true);
    assert_eq!(
        LoopLocality::check(
            &fixture.func,
            fixture.blocks.iter().copied(),
            fixture.header,
            &raise_plan(&fixture),
            Handoff::HeaderOrExit,
            &[gpr(IV)],
        )
        .map(|_| ()),
        Err(LoopStateEscape::Live {
            reg: StateReg::Virtual(gpr(TMP)),
            into: Block(5),
        })
    );
}

#[test]
fn a_raise_block_behind_an_unproven_guard_is_still_refused() {
    // The guard compares against an unrelated length, so the plan cannot prove
    // it never fires. The edge is then an exit the plan does not account for,
    // and the control check refuses before liveness is consulted.
    let fixture = x86_raise_guard_fixture(LEN, false);
    assert_eq!(
        LoopLocality::check(
            &fixture.func,
            fixture.blocks.iter().copied(),
            fixture.header,
            &raise_plan(&fixture),
            Handoff::HeaderOrExit,
            &[gpr(IV)],
        )
        .map(|_| ()),
        Err(LoopStateEscape::Exit(LoopExit::Edge {
            from: Block(2),
            to: Block(5),
        }))
    );
}
