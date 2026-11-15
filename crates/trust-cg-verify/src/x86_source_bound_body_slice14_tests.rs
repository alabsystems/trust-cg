// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 14 of the x86-64 source-bound body theorem: definedness and
//! dispatch. Division and remainder (`Udiv`, `Urem`, `Sdiv`, `Srem`) with
//! trust-ir's undefined behaviour as a per-path domain premise and the
//! machine's `div`/`idiv` #DE as a stop the theorem refutes wherever the
//! source is defined; the divide-by-zero guard (`GuardDivZero`, the
//! `TrapDivZeroExact` carrier) as an observable trap; a `Switch` several of
//! whose cases (or a case and its default) share a target, one edge of a
//! disjunctive test reached by several machine routes; and the selector's
//! jump-table dispatch, the indirect `jmp` stated from the table's own
//! targets.
//!
//! Fixtures are real: LIR from the trust-ir adapter and the machine stream
//! from the real x86-64 instruction selector (`super::select`). Wrong
//! lowerings mutate that stream and must build a theorem the sampler refutes
//! (the qualification test asks AY for each counterexample).
//!
//! Every test here runs without a solver (the `x86_source_bound_body::tests::
//! slice14::` library gate); the replay on AY and Clean and the verifier
//! credit are in `slice14_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::*;
use trust_ir::{Constant, ICmpOp, ProofAnnotation, SwitchCase};

/// Slice-14 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefinedShape {
    // ---- (a) division: undefined behaviour as a per-path premise
    /// `fn(a: u64, b: u64) -> u64 { if b == 0 { trap } a / b }`: the
    /// bridge's shape (the check, then `xor edx, edx; div`).
    UdivChecked,
    /// `fn(a: u32, b: u32) -> u32 { if b == 0 { trap } a % b }`.
    UremChecked32,
    /// `fn(a: i64, b: i64) -> i64 { if b == 0 { trap } a / b }` (`MIN / -1`
    /// is undefined: a premise; the selector's `cmov` fixup computes it).
    SdivChecked,
    /// `fn(a: i32, b: i32) -> i32 { if b == 0 { trap } a % b }`.
    SremChecked32,
    /// `fn(a: u64, b: u64) -> u64 { a / b }`: undefined at `b == 0`.
    UdivUnchecked,
    /// `fn(a: u8, b: u8) -> u8 { a / b }`: both operands zero-extended.
    UdivNarrow,
    /// `fn(a: i16, b: i16) -> i16 { a / b }`: sign-extended, `cdq; idiv`.
    SdivNarrow16,
    /// `fn(a: u64, b: u64, c: u64) -> u64 { (a / b) ^ c }`: RDX holds `c`
    /// at entry, so the dividend's high half matters.
    UdivThree,
    /// `fn(a: i64, b: i64, c: i64) -> i64 { (a / b) ^ c }`.
    SdivThree,
    /// `fn(a: u64) -> u64 { a / 10 }`: the selector's magic multiply.
    UdivConst,
    /// `fn(a: u32) -> u32 { a % 1000 }`.
    UremConst32,
    /// `fn(a: u64) -> u64 { a / 8 }`: the magic multiply by a power of two.
    UdivPow2,
    /// `fn(a: u32) -> u32 { a % 16 }`.
    UremPow2_32,
    /// `fn(a: u64, b: u64) -> u64 { let q = a / b; sink(q); q }`: the call
    /// after the undefined point.
    DivThenCall,
    /// `fn(a: u64, b: u64) -> u64 { sink(a); a / b }`: the call before it.
    CallThenDiv,
    /// `fn(a: u64, b: u64, c: u64) -> u64 { let r = if c != 0 { a / b } else
    /// { b + 1 }; r ^ c }`: the else path divides nothing.
    DivOnOnePath,
    // ---- (b) the divide-by-zero guard: an observable trap
    /// `fn(a: u64, b: u64) -> u64 { a / b }` annotated `DivNonZero`: a live
    /// guard (`TrapDivZeroExact; xor; div`).
    GuardedUdiv,
    /// `fn(a: i32, b: i32) -> i32 { a % b }` annotated `DivNonZero`.
    GuardedSrem32,
    /// The bridge's shape: `if b == 0 { trap }`, then the annotated `a / b`
    /// (a guard the check makes dead).
    GuardedChecked,
    /// The annotated `a / b`, then `sink(q)`: a trap before an event.
    GuardThenCall,
    // ---- (c) a `Switch` several of whose edges share a target
    /// `fn(x: u8) -> u64 { match x { 43 | 45 => 1, _ => 2 } }`
    /// (`from_ascii_radix`'s sign test).
    SharedCases,
    /// `fn(x: u32) -> u64 { match x { 1 => 10, 2 | _ => 30 } }`: a case
    /// shares the default's block.
    SharedDefault,
    /// `fn(x: u64) -> u64 { match x { 1 | 9 | 33 => 1, 70 => 2, _ => 3 } }`.
    SharedThree,
    /// `switch x [1 -> join(a), 2 -> join(b)], default join(c)`: the cases
    /// reach one join with different arguments, through the adapter's copy
    /// blocks.
    CaseArgs,
    // ---- (d) jump tables
    /// `fn(x: u8) -> u64 { match x { 0 => 10, 1 => 11, 2 => 12, 3 => 13, _
    /// => 0 } }`: a dense switch, a jump table.
    JumpTable,
    /// `fn(x: u64) -> u64 { match x { 0 | 1 => 1, 2 => 2, 3 | 4 => 3, _ =>
    /// 4 } }`: shared targets in a table.
    JumpTableShared,
    /// `fn(x: u32) -> u64 { match x { 0 => 1, 1 => 2, 3 => 3, 4 | _ => 4 }
    /// }`: a hole at 2 (the default's entry), which also shares case 4's
    /// block.
    JumpTableHoles,
    /// `fn(x: u32) -> u64 { match x { 10 => 1, 11 => 2, 12 => 3, 13 => 4, _
    /// => 0 } }`: the table indexed from 10.
    JumpTableOffset,
}

/// Every slice-14 shape; each is admitted and its theorem holds
/// ([`owner_builds_every_slice_fourteen_shape_and_its_theorem_holds`]).
pub(crate) const SLICE_FOURTEEN: [DefinedShape; 28] = [
    DefinedShape::UdivChecked,
    DefinedShape::UremChecked32,
    DefinedShape::SdivChecked,
    DefinedShape::SremChecked32,
    DefinedShape::UdivUnchecked,
    DefinedShape::UdivNarrow,
    DefinedShape::SdivNarrow16,
    DefinedShape::UdivThree,
    DefinedShape::SdivThree,
    DefinedShape::UdivConst,
    DefinedShape::UremConst32,
    DefinedShape::UdivPow2,
    DefinedShape::UremPow2_32,
    DefinedShape::DivThenCall,
    DefinedShape::CallThenDiv,
    DefinedShape::DivOnOnePath,
    DefinedShape::GuardedUdiv,
    DefinedShape::GuardedSrem32,
    DefinedShape::GuardedChecked,
    DefinedShape::GuardThenCall,
    DefinedShape::SharedCases,
    DefinedShape::SharedDefault,
    DefinedShape::SharedThree,
    DefinedShape::CaseArgs,
    DefinedShape::JumpTable,
    DefinedShape::JumpTableShared,
    DefinedShape::JumpTableHoles,
    DefinedShape::JumpTableOffset,
];

impl DefinedShape {
    pub(crate) fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s14_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// `if test == 0 { trap }` from the current block, which continues in a new
/// block (the bridge's divide-by-zero check, a bare trap for its panic).
fn trap_if_zero(f: &mut Builder<'_>, ty: Ty, test: V) {
    let (trap, go) = (f.create_block(), f.create_block());
    let zero = f.iconst(ty.clone(), 0);
    let is_zero = f.icmp(ICmpOp::Eq, ty, test, zero);
    f.condbr(is_zero, trap, vec![], go, vec![]);
    f.switch_to_block(trap);
    f.unreachable();
    f.switch_to_block(go);
}

/// A switch on `x` whose arms return the constants `values` (cases in order,
/// then the default), `targets[k]` naming the arm case `k` reaches (the
/// default's arm is the last).
fn returning_switch(f: &mut Builder<'_>, x: V, cases: &[i128], targets: &[usize], arms: usize) {
    let blocks: Vec<_> = (0..arms).map(|_| f.create_block()).collect();
    f.switch(
        x,
        cases
            .iter()
            .zip(targets)
            .map(|(value, target)| SwitchCase {
                value: Constant::Int(*value),
                target: blocks[*target],
                args: vec![],
            })
            .collect(),
        blocks[arms - 1],
        vec![],
    );
    for (k, block) in blocks.iter().enumerate() {
        f.switch_to_block(*block);
        let value = f.iconst(Ty::U64, 10 + k as i128);
        f.ret(vec![value]);
    }
}

/// The LIR the trust-ir adapter produces for a slice-14 shape.
pub(crate) fn slice14_lir(shape: DefinedShape) -> Function {
    use DefinedShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice14");
    let sink = {
        let ty = builder.add_func_type(vec![Ty::U64], vec![]);
        builder.declare_function("sink", ty)
    };
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        UdivChecked | UdivUnchecked | DivThenCall | CallThenDiv | GuardedUdiv | GuardedChecked
        | GuardThenCall => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        UremChecked32 => (vec![Ty::U32, Ty::U32], vec![Ty::U32]),
        SdivChecked => (vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        SremChecked32 | GuardedSrem32 => (vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        UdivNarrow => (vec![Ty::U8, Ty::U8], vec![Ty::U8]),
        SdivNarrow16 => (vec![Ty::I16, Ty::I16], vec![Ty::I16]),
        UdivThree | DivOnOnePath => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        SdivThree => (vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
        UdivConst | UdivPow2 => (vec![Ty::U64], vec![Ty::U64]),
        UremConst32 | UremPow2_32 => (vec![Ty::U32], vec![Ty::U32]),
        SharedCases | JumpTable => (vec![Ty::U8], vec![Ty::U64]),
        SharedDefault | JumpTableHoles | JumpTableOffset => (vec![Ty::U32], vec![Ty::U64]),
        SharedThree | JumpTableShared => (vec![Ty::U64], vec![Ty::U64]),
        CaseArgs => (vec![Ty::U64, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let nonzero = || vec![ProofAnnotation::DivNonZero];
    match shape {
        UdivChecked | UremChecked32 | SdivChecked | SremChecked32 => {
            let (ty, op) = match shape {
                UdivChecked => (Ty::U64, BinOp::UDiv),
                UremChecked32 => (Ty::U32, BinOp::URem),
                SdivChecked => (Ty::I64, BinOp::SDiv),
                _ => (Ty::I32, BinOp::SRem),
            };
            trap_if_zero(&mut f, ty.clone(), args[1]);
            let q = f.binop(op, ty, args[0], args[1]);
            f.ret(vec![q]);
        }
        UdivUnchecked | UdivNarrow | SdivNarrow16 => {
            let (ty, op) = match shape {
                UdivUnchecked => (Ty::U64, BinOp::UDiv),
                UdivNarrow => (Ty::U8, BinOp::UDiv),
                _ => (Ty::I16, BinOp::SDiv),
            };
            let q = f.binop(op, ty, args[0], args[1]);
            f.ret(vec![q]);
        }
        UdivThree | SdivThree => {
            let (ty, op) = if shape == UdivThree {
                (Ty::U64, BinOp::UDiv)
            } else {
                (Ty::I64, BinOp::SDiv)
            };
            let q = f.binop(op, ty.clone(), args[0], args[1]);
            let r = f.binop(BinOp::Xor, ty, q, args[2]);
            f.ret(vec![r]);
        }
        UdivConst => {
            let ten = f.iconst(Ty::U64, 10);
            let q = f.binop(BinOp::UDiv, Ty::U64, args[0], ten);
            f.ret(vec![q]);
        }
        UremConst32 => {
            let thousand = f.iconst(Ty::U32, 1000);
            let r = f.binop(BinOp::URem, Ty::U32, args[0], thousand);
            f.ret(vec![r]);
        }
        UdivPow2 => {
            let eight = f.iconst(Ty::U64, 8);
            let q = f.binop(BinOp::UDiv, Ty::U64, args[0], eight);
            f.ret(vec![q]);
        }
        UremPow2_32 => {
            let sixteen = f.iconst(Ty::U32, 16);
            let r = f.binop(BinOp::URem, Ty::U32, args[0], sixteen);
            f.ret(vec![r]);
        }
        DivThenCall => {
            let q = f.binop(BinOp::UDiv, Ty::U64, args[0], args[1]);
            f.call_void(sink, vec![q]);
            f.ret(vec![q]);
        }
        CallThenDiv => {
            f.call_void(sink, vec![args[0]]);
            let q = f.binop(BinOp::UDiv, Ty::U64, args[0], args[1]);
            f.ret(vec![q]);
        }
        DivOnOnePath => {
            let (divide, add, join) = (f.create_block(), f.create_block(), f.create_block());
            let r = f.add_block_param(join, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let go = f.icmp(ICmpOp::Ne, Ty::U64, args[2], zero);
            f.condbr(go, divide, vec![], add, vec![]);
            f.switch_to_block(divide);
            let q = f.binop(BinOp::UDiv, Ty::U64, args[0], args[1]);
            f.br(join, vec![q]);
            f.switch_to_block(add);
            let one = f.iconst(Ty::U64, 1);
            let s = f.add(Ty::U64, args[1], one);
            f.br(join, vec![s]);
            f.switch_to_block(join);
            let out = f.binop(BinOp::Xor, Ty::U64, r, args[2]);
            f.ret(vec![out]);
        }
        GuardedUdiv | GuardThenCall => {
            let q = f.binop_proven(BinOp::UDiv, Ty::U64, args[0], args[1], nonzero());
            if shape == GuardThenCall {
                f.call_void(sink, vec![q]);
            }
            f.ret(vec![q]);
        }
        GuardedSrem32 => {
            let r = f.binop_proven(BinOp::SRem, Ty::I32, args[0], args[1], nonzero());
            f.ret(vec![r]);
        }
        GuardedChecked => {
            trap_if_zero(&mut f, Ty::U64, args[1]);
            let q = f.binop_proven(BinOp::UDiv, Ty::U64, args[0], args[1], nonzero());
            f.ret(vec![q]);
        }
        SharedCases => returning_switch(&mut f, args[0], &[43, 45], &[0, 0], 2),
        SharedDefault => returning_switch(&mut f, args[0], &[1, 2], &[0, 1], 2),
        SharedThree => returning_switch(&mut f, args[0], &[1, 9, 33, 70], &[0, 0, 0, 1], 3),
        CaseArgs => {
            let join = f.create_block();
            let v = f.add_block_param(join, Ty::U64);
            f.switch(
                args[0],
                vec![
                    SwitchCase {
                        value: Constant::Int(1),
                        target: join,
                        args: vec![args[1]],
                    },
                    SwitchCase {
                        value: Constant::Int(2),
                        target: join,
                        args: vec![args[2]],
                    },
                ],
                join,
                vec![args[3]],
            );
            f.switch_to_block(join);
            f.ret(vec![v]);
        }
        JumpTable => returning_switch(&mut f, args[0], &[0, 1, 2, 3], &[0, 1, 2, 3], 5),
        JumpTableShared => returning_switch(&mut f, args[0], &[0, 1, 2, 3, 4], &[0, 0, 1, 2, 2], 4),
        JumpTableHoles => returning_switch(&mut f, args[0], &[0, 1, 3, 4], &[0, 1, 2, 3], 4),
        JumpTableOffset => returning_switch(&mut f, args[0], &[10, 11, 12, 13], &[0, 1, 2, 3], 5),
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice14_pair(shape: DefinedShape) -> (Function, X86ISelFunction) {
    let source = slice14_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

/// The walk ordinal of the copy of a division's result out of `root` (RAX
/// for a quotient, RDX for a remainder; the 32-bit alias for a narrow one).
fn result_copy(machine: &X86ISelFunction, root: u16) -> usize {
    row_where(machine, |row| {
        matches!(row.opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
            && matches!(&row.operands[1], O::PReg(preg) if preg.encoding() % 16 == root)
            && matches!(row.operands[0], O::VReg(_))
    })
}

/// The machine block whose rows are stamped with LIR block `lir`, and the
/// table of a jump-table fixture.
fn lowering_of(machine: &X86ISelFunction, lir: Block) -> Block {
    machine
        .block_order
        .iter()
        .copied()
        .find(|block| {
            machine.blocks[block].insts.iter().any(|inst| {
                inst.lowering_provenance
                    .source_id()
                    .is_some_and(|id| id.block == lir.0)
            })
        })
        .expect("a machine block lowers it")
}

/// Every wrong lowering of a slice-14 fixture, labelled: each must build a
/// theorem that is refuted (the qualification test asks AY for each
/// counterexample).
pub(crate) fn slice_fourteen_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use DefinedShape::*;
    let mut out = Vec::new();
    let mut push = |label: &'static str, source: Function, machine: X86ISelFunction| {
        out.push((label, source, machine));
    };
    // A missing `cqo`: RDX still holds the third argument.
    let (source, mut machine) = slice14_pair(SdivThree);
    let cqo = row_where(&machine, |row| row.opcode == X86Opcode::Cqo);
    remove_at(&mut machine, cqo);
    push("a missing cqo", source, machine);
    // `cdq` where `cqo` is needed.
    let (source, mut machine) = slice14_pair(SdivThree);
    let cqo = row_where(&machine, |row| row.opcode == X86Opcode::Cqo);
    inst_mut(&mut machine, cqo).opcode = X86Opcode::Cdq;
    push("cdq where cqo is needed", source, machine);
    // A missing `xor edx, edx`: RDX still holds the third argument.
    let (source, mut machine) = slice14_pair(UdivThree);
    let xor = row_where(&machine, |row| row.opcode == X86Opcode::XorRR);
    remove_at(&mut machine, xor);
    push("a missing rdx zeroing", source, machine);
    // The dividend taken from another register (the third argument): the
    // same divisor, so the same #DE, and a quotient of other operands (the
    // division's pairing with the source's must not apply,
    // [`pair_divisions`]).
    let (source, mut machine) = slice14_pair(UdivThree);
    let third = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRR && row.operands[1] == preg(RDX)
    });
    let third = inst(&machine, third).operands[0].clone();
    let dividend = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRR && row.operands[0] == preg(RAX)
    });
    inst_mut(&mut machine, dividend).operands[1] = third;
    push("the dividend from another register", source, machine);
    // The remainder returned for the quotient.
    let (source, mut machine) = slice14_pair(UdivUnchecked);
    let copy = result_copy(&machine, RAX);
    inst_mut(&mut machine, copy).operands[1] = preg(RDX);
    push("the remainder for the quotient", source, machine);
    // The quotient returned for the remainder.
    let (source, mut machine) = slice14_pair(UremChecked32);
    let copy = result_copy(&machine, RDX);
    inst_mut(&mut machine, copy).operands[1] = preg(GPR32_ALIAS_BASE + RAX);
    push("the quotient for the remainder", source, machine);
    // An unsigned `div` for a signed division, and the reverse.
    let (source, mut machine) = slice14_pair(SdivChecked);
    let idiv = row_where(&machine, |row| row.opcode == X86Opcode::Idiv);
    inst_mut(&mut machine, idiv).opcode = X86Opcode::Div;
    push("div for idiv", source, machine);
    let (source, mut machine) = slice14_pair(UdivUnchecked);
    let div = row_where(&machine, |row| row.opcode == X86Opcode::Div);
    inst_mut(&mut machine, div).opcode = X86Opcode::Idiv;
    push("idiv for div", source, machine);
    // A narrow divisor not zero-extended (its register's bits above 8 are
    // the caller's).
    let (source, mut machine) = slice14_pair(UdivNarrow);
    let div = row_where(&machine, |row| row.opcode == X86Opcode::Div);
    let divisor = inst(&machine, div).operands[0].clone();
    let extend = row_where(&machine, |row| {
        matches!(row.opcode, X86Opcode::Movzx | X86Opcode::MovzxW) && row.operands[0] == divisor
    });
    let raw = match inst(&machine, extend).operands[1].clone() {
        O::VReg(vreg) => O::VReg(VReg::new(vreg.id, RegClass::Gpr32)),
        other => other,
    };
    let row = inst_mut(&mut machine, extend);
    row.opcode = X86Opcode::MovRR32;
    row.operands[1] = raw;
    assert_eq!(inst(&machine, extend).opcode, X86Opcode::MovRR32);
    push("a narrow divisor not extended", source, machine);
    // The magic multiplier off by one.
    let (source, mut machine) = slice14_pair(UdivConst);
    let magic = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRI
            && matches!(row.operands[1], O::Imm(imm) if imm.unsigned_abs() > 1 << 32)
    });
    if let O::Imm(imm) = &mut inst_mut(&mut machine, magic).operands[1] {
        *imm += 1;
    }
    push("the magic multiplier off by one", source, machine);
    // A dropped guard: the `div` faults where the source traps.
    let (source, mut machine) = slice14_pair(GuardedUdiv);
    let guard = row_where(&machine, |row| row.opcode == X86Opcode::TrapDivZeroExact);
    remove_at(&mut machine, guard);
    push("a dropped guard", source, machine);
    // The guard on the dividend.
    let (source, mut machine) = slice14_pair(GuardedUdiv);
    let guard = row_where(&machine, |row| row.opcode == X86Opcode::TrapDivZeroExact);
    let dividend = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRR && row.operands[0] == preg(RAX)
    });
    let dividend = inst(&machine, dividend).operands[1].clone();
    inst_mut(&mut machine, guard).operands[0] = dividend;
    push("the guard on the dividend", source, machine);
    // A guard after the call it must come before.
    let (source, mut machine) = slice14_pair(GuardThenCall);
    let guard = row_where(&machine, |row| row.opcode == X86Opcode::TrapDivZeroExact);
    let removed = remove_at(&mut machine, guard);
    let call = row_where(&machine, |row| row.opcode == X86Opcode::Call);
    insert_at(&mut machine, call + 1, removed);
    push("a guard after the call", source, machine);
    // A trap on the path that divides nothing.
    let (source, mut machine) = slice14_pair(DivOnOnePath);
    let add = row_where(&machine, |row| {
        row.opcode == X86Opcode::AddRI || row.opcode == X86Opcode::AddRR
    });
    let b = inst(&machine, add).operands[1].clone();
    insert_at(
        &mut machine,
        add,
        X86ISelInst::new(X86Opcode::TrapDivZeroExact, vec![b]),
    );
    push("a trap the source does not take", source, machine);
    // The division hoisted above its branch, into the entry block (restamped
    // with the entry's LIR block, so the block correspondence still holds):
    // it faults on the path that divides nothing.
    let (source, mut machine) = slice14_pair(DivOnOnePath);
    let entry = machine.block_order[0];
    let entry_stamp = machine.blocks[&entry].insts[0].lowering_provenance;
    let div = row_where(&machine, |row| row.opcode == X86Opcode::Div);
    let first = row_where(&machine, |row| {
        row.opcode == X86Opcode::XorRR && row.operands[0] == preg(RDX)
    })
    .min(row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRR && row.operands[0] == preg(RAX)
    }));
    let copy = div + 1;
    let mut moved: Vec<X86ISelInst> = (first..=copy)
        .map(|_| remove_at(&mut machine, first))
        .collect();
    for row in &mut moved {
        row.lowering_provenance = entry_stamp;
    }
    let branch = row_where(&machine, |row| {
        matches!(
            row.opcode,
            X86Opcode::CmpRI | X86Opcode::CmpRR | X86Opcode::TestRR
        )
    });
    for (offset, row) in moved.into_iter().enumerate() {
        insert_at(&mut machine, branch + offset, row);
    }
    push("the division hoisted above its branch", source, machine);
    // An extra division by zero after the quotient is copied out.
    let (source, mut machine) = slice14_pair(UdivUnchecked);
    let copy = result_copy(&machine, RAX);
    let zero = fresh(9000);
    insert_at(
        &mut machine,
        copy + 1,
        X86ISelInst::new(X86Opcode::MovRI, vec![zero.clone(), O::Imm(0)]),
    );
    insert_at(
        &mut machine,
        copy + 2,
        X86ISelInst::new(X86Opcode::Div, vec![zero]),
    );
    push("an extra division by zero", source, machine);
    // A shared case's compare of another value.
    let (source, mut machine) = slice14_pair(SharedCases);
    let compare = row_where(&machine, |row| {
        row.opcode == X86Opcode::CmpRI && row.operands[1] == O::Imm(45)
    });
    inst_mut(&mut machine, compare).operands[1] = O::Imm(46);
    push("a shared case compared with another value", source, machine);
    // A shared case sent to the default's block.
    let (source, mut machine) = slice14_pair(SharedCases);
    let jumps = find(&machine, X86Opcode::Jcc);
    let default = match inst(&machine, *jumps.last().unwrap() + 1)
        .operands
        .as_slice()
    {
        [O::Block(target)] => *target,
        other => panic!("the default's jmp: {other:?}"),
    };
    inst_mut(&mut machine, jumps[1]).operands[1] = O::Block(default);
    push("a shared case sent to the default", source, machine);
    // Two cases' arguments swapped (their copy blocks' sources).
    let (source, mut machine) = slice14_pair(CaseArgs);
    let copies: Vec<usize> = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovRR
                && matches!(row.operands[1], O::VReg(vreg) if vreg.id == 2 || vreg.id == 3)
        })
        .collect();
    let (first, second) = (
        inst(&machine, copies[0]).operands[1].clone(),
        inst(&machine, copies[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, copies[0]).operands[1] = second;
    inst_mut(&mut machine, copies[1]).operands[1] = first;
    push("two cases' arguments swapped", source, machine);
    // A wrong jump-table entry (two entries swapped: the targets as a set,
    // and so the dispatch block's successors, unchanged).
    let (source, mut machine) = slice14_pair(JumpTable);
    machine.jump_tables[0].targets.swap(0, 1);
    push("two jump-table entries swapped", source, machine);
    // The bound check one short.
    let (source, mut machine) = slice14_pair(JumpTable);
    let bound = row_where(&machine, |row| {
        row.opcode == X86Opcode::CmpRI && row.operands[1] == O::Imm(3)
    });
    inst_mut(&mut machine, bound).operands[1] = O::Imm(2);
    push("the jump-table bound one short", source, machine);
    // The table's first case not subtracted.
    let (source, mut machine) = slice14_pair(JumpTableOffset);
    let subtract = row_where(&machine, |row| {
        row.opcode == X86Opcode::SubRI && row.operands.last() == Some(&O::Imm(10))
    });
    remove_at(&mut machine, subtract);
    push("the table's first case not subtracted", source, machine);
    // A 32-bit selector copied into the 64-bit index with a 64-bit `mov`
    // (the selector's form before slice 14): the `Gpr32` vreg's bits above
    // 31, which this stream does not define, reach the bound check and the
    // index. (Natively that form returned the right values where measured;
    // the stream, not the emitted code, is what this refutes.)
    let (source, mut machine) = slice14_pair(JumpTableHoles);
    let copy = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovRR32
            && matches!(row.operands.as_slice(), [O::VReg(norm), O::VReg(selector)]
                if norm.class == RegClass::Gpr64 && selector.class == RegClass::Gpr32)
    });
    inst_mut(&mut machine, copy).opcode = X86Opcode::MovRR;
    push(
        "a 32-bit selector copied with a 64-bit mov",
        source,
        machine,
    );
    // A hole's entry sent to a case's block.
    let (source, mut machine) = slice14_pair(JumpTableHoles);
    let first_case = machine.jump_tables[0].targets[0];
    machine.jump_tables[0].targets[2] = first_case;
    push("a hole's entry sent to a case", source, machine);
    out
}

/// A fresh 64-bit virtual register.
fn fresh(id: u32) -> O {
    O::VReg(VReg::new(id, RegClass::Gpr64))
}

/// The theorem of a pair, or (a pair the owner refuses) why.
#[track_caller]
fn theorem(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    theorem_without_affine_refusal(source, machine, SYSV).unwrap_or_else(|refusal| {
        panic!(
            "{what}: {refusal}\n{}{}",
            describe_lir(source),
            describe(machine)
        )
    })
}

/// Every slice-14 fixture is admitted, and its theorem holds on the
/// structured samples (every constant of the theorem, zero and the
/// carriers' extremes among them).
#[test]
fn owner_builds_every_slice_fourteen_shape_and_its_theorem_holds() {
    for shape in SLICE_FOURTEEN {
        let (source, machine) = slice14_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            dag_holds_on_samples(&obligation),
            "{shape:?}: a correct lowering is refuted\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
    }
}

/// Every wrong lowering builds a theorem the sampler refutes.
#[test]
fn every_slice_fourteen_refutation_is_refuted() {
    for (label, source, machine) in slice_fourteen_refutations() {
        let obligation = theorem(&source, &machine, label);
        assert!(
            dag_refuted_on_samples(&obligation),
            "{label}: a wrong lowering is not refuted\n{}",
            describe(&machine)
        );
    }
}

/// The fixtures have the machine shapes they are meant to exercise: the
/// selector's `xor edx, edx; div`, `cqo`/`cdq; idiv`, the narrow
/// extensions, the magic multiply, the guard carrier, the compare chains
/// with several `je`s to one block, and the jump-table dispatch.
#[test]
fn slice_fourteen_fixtures_have_their_machine_shapes() {
    use DefinedShape::*;
    let has = |shape: DefinedShape, opcode: X86Opcode| {
        let (_, machine) = slice14_pair(shape);
        !find(&machine, opcode).is_empty()
    };
    for shape in [
        UdivChecked,
        UdivUnchecked,
        UdivThree,
        DivThenCall,
        CallThenDiv,
    ] {
        assert!(has(shape, X86Opcode::Div), "{shape:?}");
        assert!(has(shape, X86Opcode::XorRR), "{shape:?}");
    }
    assert!(has(SdivChecked, X86Opcode::Cqo) && has(SdivChecked, X86Opcode::Idiv));
    assert!(has(SremChecked32, X86Opcode::Cdq) && has(SremChecked32, X86Opcode::Idiv));
    assert!(has(SdivNarrow16, X86Opcode::MovsxW) && has(SdivNarrow16, X86Opcode::Cdq));
    assert!(has(UdivNarrow, X86Opcode::Movzx));
    assert!(has(UdivConst, X86Opcode::Mul) && !has(UdivConst, X86Opcode::Div));
    for shape in [GuardedUdiv, GuardedSrem32, GuardedChecked, GuardThenCall] {
        assert!(has(shape, X86Opcode::TrapDivZeroExact), "{shape:?}");
    }
    for shape in [SharedCases, SharedDefault, SharedThree] {
        let (source, machine) = slice14_pair(shape);
        let switch_block = source
            .blocks
            .iter()
            .find(|(_, block)| {
                matches!(
                    block.instructions.last().map(|inst| &inst.opcode),
                    Some(L::Switch { .. })
                )
            })
            .map(|(id, _)| *id)
            .expect("a switch");
        let lowered = lowering_of(&machine, switch_block);
        let mut targets: Vec<Block> = machine.blocks[&lowered]
            .insts
            .iter()
            .filter_map(|inst| match inst.operands.as_slice() {
                [O::CondCode(_), O::Block(target)] | [O::Block(target)] => Some(*target),
                _ => None,
            })
            .collect();
        let all = targets.len();
        targets.sort();
        targets.dedup();
        assert!(
            targets.len() < all,
            "{shape:?}: no two transfers share a block"
        );
    }
    for shape in [JumpTable, JumpTableShared, JumpTableHoles, JumpTableOffset] {
        let (_, machine) = slice14_pair(shape);
        assert_eq!(machine.jump_tables.len(), 1, "{shape:?}");
        assert_eq!(dispatch_blocks(&machine).len(), 1, "{shape:?}");
    }
    assert!(has(JumpTableOffset, X86Opcode::SubRI));
}

/// The verify-owned meaning of LIR `Udiv`/`Urem`/`Sdiv`/`Srem`
/// ([`division`]) and its undefinedness ([`division_undefined`]) are the
/// pinned trust-ir interpreter's, at every width and on the edge operands:
/// where the interpreter returns a value the stated one equals it, and the
/// stated undefinedness holds exactly where it reports undefined behaviour.
#[test]
fn the_division_meanings_are_trust_irs() {
    use crate::smt::{EvalEnv, EvalResult};
    use trust_ir::interpret::{
        InterpretErrorCode, InterpretInt, InterpretValue, InterpretValueKind,
    };
    let ops = [
        (BinOp::UDiv, false, false, "udiv"),
        (BinOp::URem, false, true, "urem"),
        (BinOp::SDiv, true, false, "sdiv"),
        (BinOp::SRem, true, true, "srem"),
    ];
    let widths = [8u32, 16, 32, 64];
    let ty_of = |bits: u32, signed: bool| match (bits, signed) {
        (8, false) => Ty::U8,
        (16, false) => Ty::U16,
        (32, false) => Ty::U32,
        (64, false) => Ty::U64,
        (8, true) => Ty::I8,
        (16, true) => Ty::I16,
        (32, true) => Ty::I32,
        _ => Ty::I64,
    };
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice14_division_meanings");
    for (op, signed, _, tag) in ops {
        for bits in widths {
            let ty = ty_of(bits, signed);
            let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
            let mut f = builder.function(format!("{tag}{bits}"), signature);
            let entry = f.create_block();
            let a = f.add_block_param(entry, ty.clone());
            let b = f.add_block_param(entry, ty.clone());
            f.switch_to_block(entry);
            let r = f.binop(op, ty, a, b);
            f.ret(vec![r]);
            f.build();
        }
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let interpreter = trust_ir::interpret::Interpreter::with_module(&module);
    for (_, signed, remainder, tag) in ops {
        for bits in widths {
            let mask = crate::smt::mask(u64::MAX, bits);
            let minimum = 1u64 << (bits - 1);
            let operands: Vec<u64> = [
                0,
                1,
                2,
                3,
                7,
                10,
                minimum - 1,
                minimum,
                minimum + 1,
                mask - 1,
                mask,
                0x5a5a_5a5a_5a5a_5a5a & mask,
            ]
            .into_iter()
            .collect();
            let function = module
                .function_by_name(&format!("{tag}{bits}"))
                .expect("the function");
            for a in &operands {
                for b in &operands {
                    let value = |raw: u64| InterpretValue {
                        ty: ty_of(bits, signed),
                        kind: InterpretValueKind::Int(
                            InterpretInt::from_raw(bits, signed, u128::from(raw))
                                .expect("in range"),
                        ),
                    };
                    let outcome =
                        interpreter.execute_function(function, vec![value(*a), value(*b)]);
                    let mut env = EvalEnv::default();
                    env.insert("a".into(), *a);
                    env.insert("b".into(), *b);
                    let (x, y) = (E::var("a", bits), E::var("b", bits));
                    let undefined = matches!(
                        division_undefined(signed, x.clone(), y.clone()).eval(&env),
                        EvalResult::Bool(true)
                    );
                    match outcome {
                        Ok(outcome) => {
                            assert!(!undefined, "{tag}{bits} {a:#x} {b:#x}: defined");
                            let [
                                InterpretValue {
                                    kind: InterpretValueKind::Int(result),
                                    ..
                                },
                            ] = &outcome.returns[..]
                            else {
                                panic!("{tag}{bits}: {:?}", outcome.returns);
                            };
                            let EvalResult::Bv(stated) =
                                division(signed, remainder, x, y).eval(&env)
                            else {
                                panic!("a bit-vector");
                            };
                            assert_eq!(u128::from(stated), result.raw, "{tag}{bits} {a:#x} {b:#x}");
                        }
                        Err(error) => {
                            assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
                            assert!(undefined, "{tag}{bits} {a:#x} {b:#x}: undefined");
                        }
                    }
                }
            }
        }
    }
}

/// The power-of-two spellings are exact: [`power_of_two_division`] is
/// [`division`] (checked against the pinned interpreter above) for every
/// unsigned width, power of two and operand class, and
/// [`power_of_two_product`] is Intel's `mul` (the wrapped product and
/// `encode_mul_high`) at 32 and 64 bits.
#[test]
fn the_power_of_two_spellings_are_exact() {
    use crate::smt::EvalEnv;
    for bits in [8u32, 16, 32, 64] {
        let mask = crate::smt::mask(u64::MAX, bits);
        let values = [
            0,
            1,
            2,
            3,
            7,
            10,
            mask >> 1,
            (mask >> 1) + 1,
            mask - 1,
            mask,
        ];
        for j in 0..bits {
            let k = 1u64 << j;
            for remainder in [false, true] {
                for a in values {
                    let x = E::var("a", bits);
                    let mut env = EvalEnv::default();
                    env.insert("a".into(), a);
                    let spelled = power_of_two_division(remainder, x.clone(), k).eval(&env);
                    let stated = division(false, remainder, x, E::bv_const(k, bits)).eval(&env);
                    assert_eq!(
                        spelled, stated,
                        "{bits} {a:#x} by {k} remainder={remainder}"
                    );
                }
            }
            if bits >= 32 {
                for a in values {
                    let x = E::var("a", bits);
                    let mut env = EvalEnv::default();
                    env.insert("a".into(), a);
                    let (low, high) = power_of_two_product(x.clone(), k);
                    let m = E::bv_const(k, bits);
                    assert_eq!(
                        low.eval(&env),
                        x.clone().bvmul(m.clone()).eval(&env),
                        "{bits} {a:#x} * {k}"
                    );
                    assert_eq!(
                        high.eval(&env),
                        crate::x86_64_semantics::encode_mul_high(x, m).eval(&env),
                        "{bits} {a:#x} * {k} high"
                    );
                }
            }
        }
    }
}

/// x86 `div`/`idiv` ([`machine_division`]) at both widths, against a direct
/// computation of Intel's DIV/IDIV over every dividend high half the walk
/// may see: zero, the low half's sign, and arbitrary bits (the general
/// double-width form). The quotient and remainder are compared wherever no
/// #DE is raised, and the #DE condition exactly.
#[test]
fn the_machine_division_is_intels() {
    use crate::smt::{EvalEnv, EvalResult};
    for bits in [32u32, 64] {
        let mask = crate::smt::mask(u64::MAX, bits);
        let minimum = 1u64 << (bits - 1);
        let values = [
            0,
            1,
            2,
            3,
            7,
            minimum - 1,
            minimum,
            minimum + 1,
            mask - 1,
            mask,
        ];
        for signed in [false, true] {
            for low in values {
                for divisor in values {
                    let sign = if low & minimum != 0 { mask } else { 0 };
                    for (high, canonical) in [
                        (0, !signed),
                        (sign, signed),
                        (1, false),
                        (mask, false),
                        (minimum, false),
                    ] {
                        let (lo, hi, d) =
                            (E::var("lo", bits), E::var("hi", bits), E::var("d", bits));
                        let definition = if !canonical {
                            None
                        } else if signed {
                            Some(widen(sign_of(lo.clone()), bits))
                        } else {
                            Some(E::bv_const(0, 64))
                        };
                        let (quotient, remainder, fault, _) =
                            machine_division(signed, lo, hi, definition.as_ref(), d);
                        let mut env = EvalEnv::default();
                        env.insert("lo".into(), low);
                        env.insert("hi".into(), high);
                        env.insert("d".into(), divisor);
                        let EvalResult::Bool(faults) = fault.eval(&env) else {
                            panic!("a boolean");
                        };
                        // Intel: the double-width dividend, the quotient
                        // truncated toward zero, #DE when it does not fit.
                        let dividend = (u128::from(high) << bits) | u128::from(low);
                        let expected = if divisor == 0 {
                            None
                        } else if signed {
                            let n = (dividend << (128 - 2 * bits)) as i128 >> (128 - 2 * bits);
                            let d = (i128::from(divisor) << (128 - bits)) >> (128 - bits);
                            // `i128::MIN / -1` (a 64-bit dividend of
                            // 2^127) does not fit either.
                            n.checked_div(d).zip(n.checked_rem(d)).and_then(|(q, r)| {
                                let fits = q >= -(1i128 << (bits - 1)) && q < (1i128 << (bits - 1));
                                fits.then_some(((q as u64) & mask, (r as u64) & mask))
                            })
                        } else {
                            let q = dividend / u128::from(divisor);
                            let r = dividend % u128::from(divisor);
                            (q <= u128::from(mask)).then_some((q as u64, r as u64))
                        };
                        let what = format!(
                            "{} {bits}: {high:#x}:{low:#x} / {divisor:#x}",
                            if signed { "idiv" } else { "div" }
                        );
                        assert_eq!(faults, expected.is_none(), "{what}: #DE");
                        if let Some((q, r)) = expected {
                            let EvalResult::Bv(stated_q) = quotient.eval(&env) else {
                                panic!("a bit-vector");
                            };
                            let EvalResult::Bv(stated_r) = remainder.eval(&env) else {
                                panic!("a bit-vector");
                            };
                            assert_eq!((stated_q, stated_r), (q, r), "{what}");
                        }
                    }
                }
            }
        }
    }
}

/// An undefined division stops the claims after it on its own path only:
/// on the path that divides nothing, every item is claimed unconditionally
/// (its stop term is the constant 0), and a trap there is refuted.
#[test]
fn an_undefined_division_is_a_premise_of_its_own_path_only() {
    let (source, machine) = slice14_pair(DefinedShape::DivOnOnePath);
    let body = admitted_body(&source).expect("admitted");
    let dag = body.dag.as_ref().expect("stated over the DAG");
    let mut stopping = 0;
    for program in dag.blocks.values() {
        let divides = program
            .definitions
            .iter()
            .any(|definition| matches!(definition.op, SourceOp::Divide { .. }));
        assert_eq!(divides, !program.stops.is_empty());
        stopping += usize::from(divides);
    }
    assert_eq!(stopping, 1, "exactly the dividing block may stop");
    assert!(dag_holds_on_samples(&owner(
        &source,
        &machine,
        "DivOnOnePath"
    )));
}

/// A defined trap is an observable, never a premise: the guard's claim
/// states that the machine's first stop is a trap carrier wherever the
/// guard fires, and a #DE in its place (the carrier dropped) is refuted.
#[test]
fn a_guard_is_an_observable_trap() {
    let (source, machine) = slice14_pair(DefinedShape::GuardedUdiv);
    let body = admitted_body(&source).expect("admitted");
    let program = &body.paths[0];
    assert!(matches!(
        program.stops.as_slice(),
        [
            SourceStop {
                kind: StopKind::Guard { .. },
                ..
            },
            SourceStop {
                kind: StopKind::Undefined { .. },
                ..
            },
        ]
    ));
    assert!(dag_holds_on_samples(&owner(
        &source,
        &machine,
        "GuardedUdiv"
    )));
    let (_, wrong, mutated) = slice_fourteen_refutations()
        .into_iter()
        .find(|(label, _, _)| *label == "a dropped guard")
        .expect("the dropped-guard refutation");
    assert!(dag_refuted_on_samples(&theorem(
        &wrong,
        &mutated,
        "a dropped guard"
    )));
}

/// What stays outside, by name: a guard bound to a discharged obligation, a
/// jump table outside the dispatch idiom, EH tables and an outgoing call
/// area. (An `I128` division, outside until slice 22, is admitted as the
/// call of its runtime routine, OD-202.)
#[test]
fn slice_fourteen_neighbours_stay_outside_by_name() {
    // A guard bound to an obligation.
    let mut source = slice14_lir(DefinedShape::GuardedUdiv);
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::GuardDivZero { obligation } = &mut inst.opcode {
                *obligation = Some(7);
            }
        }
    }
    match admitted_body(&source) {
        Err(refusal) => assert!(
            refusal.to_string().contains("discharged obligation"),
            "{refusal}"
        ),
        Ok(_) => panic!("a bound guard is admitted"),
    }
    // An `I128` division.
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice14_wide_division");
    let signature = builder.add_func_type(vec![Ty::U128, Ty::U128], vec![Ty::U128]);
    let mut f = builder.function("s14_udiv_u128", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U128);
    let b = f.add_block_param(entry, Ty::U128);
    f.switch_to_block(entry);
    let q = f.binop(BinOp::UDiv, Ty::U128, a, b);
    f.ret(vec![q]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("translates")
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s14_udiv_u128")
    .expect("translated");
    // Slice 22 (OD-202) admits it: the call of its runtime routine
    // (`slice22`), with no division stated.
    if let Err(refusal) = admitted_body(&source) {
        panic!("an i128 division is the call of its routine since slice 22: {refusal}");
    }
    // A jump table whose dispatch is not the selector's idiom.
    let (source, mut machine) = slice14_pair(DefinedShape::JumpTable);
    let jump = row_where(&machine, |row| row.opcode == X86Opcode::JmpR);
    let lea = row_where(&machine, |row| {
        row.opcode == X86Opcode::LeaRip && matches!(row.operands[1], O::JumpTableIndex(_))
    });
    let base = inst(&machine, lea).operands[0].clone();
    inst_mut(&mut machine, jump).operands[0] = base;
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            assert!(reason.to_string().contains("jump table"), "{reason}")
        }
        other => panic!("a jump through the table's base: {:?}", other.err()),
    }
    // Guard obligations (the kernel may delete a carrier).
    let (source, mut machine) = slice14_pair(DefinedShape::GuardedUdiv);
    machine.guard_obligations.insert(1, 2);
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            assert!(reason.to_string().contains("guard obligations"), "{reason}")
        }
        other => panic!("guard obligations: {:?}", other.err()),
    }
    // A table read by a row other than its dispatch's `lea`.
    let (source, mut machine) = slice14_pair(DefinedShape::JumpTable);
    let entry = machine.block_order[0];
    machine.blocks.get_mut(&entry).unwrap().insts.insert(
        0,
        X86ISelInst::new(X86Opcode::LeaRip, vec![fresh(9100), O::JumpTableIndex(0)]),
    );
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            assert!(reason.to_string().contains("jump table 0"), "{reason}")
        }
        other => panic!("a second reference to the table: {:?}", other.err()),
    }
    // An outgoing call area.
    let (source, mut machine) = slice14_pair(DefinedShape::JumpTable);
    machine.max_outgoing_call_bytes = 16;
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            assert!(
                reason.to_string().contains("outgoing call area"),
                "{reason}"
            )
        }
        other => panic!("an outgoing call area: {:?}", other.err()),
    }
}

/// A shared `Switch` target is one source edge whose test is the
/// disjunction of its cases' (and the default's), and its machine side is
/// every route of the compare chain to the block.
#[test]
fn a_shared_switch_target_is_one_edge() {
    let (source, _) = slice14_pair(DefinedShape::SharedThree);
    let cfg = source_cfg(&source).expect("a CFG");
    assert!(cfg.shared_targets);
    let body = admitted_body(&source).expect("admitted");
    let dag = body.dag.as_ref().expect("stated over the DAG");
    let switching = dag
        .blocks
        .values()
        .find(|program| {
            program
                .branches
                .iter()
                .any(|branch| matches!(branch.test, BranchTest::Cases { .. }))
        })
        .expect("the switch block");
    let tests: Vec<&BranchTest> = switching
        .branches
        .iter()
        .map(|branch| &branch.test)
        .collect();
    assert_eq!(
        tests,
        [
            &BranchTest::Cases {
                cases: vec![1, 9, 33],
                default: None
            },
            &BranchTest::Case(70),
            &BranchTest::Default(vec![1, 9, 33, 70]),
        ]
    );
}

/// Building a pair again gives the same theorem.
#[test]
fn slice_fourteen_theorems_are_deterministic() {
    for shape in SLICE_FOURTEEN {
        let (source, machine) = slice14_pair(shape);
        let first = owner(&source, &machine, &format!("{shape:?}"));
        let second = owner(&source, &machine, &format!("{shape:?}"));
        assert_eq!(first, second, "{shape:?}");
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-14
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_fourteen_fixtures_are_judged_without_false_mismatches() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        for shape in SLICE_FOURTEEN {
            let (source, mut machine) = slice14_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match source_bound_x86_body(&source, &machine, SYSV) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        dag_holds_on_samples(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                    eprintln!("{opt_level:?} {shape:?}: theorem holds on samples");
                }
                Err(X86BodyRefusal::Unsupported(refusal)) => {
                    eprintln!("{opt_level:?} {shape:?}: no claim ({refusal})");
                }
                Err(other) => panic!(
                    "{shape:?} at {opt_level:?}: {other}\n{}",
                    describe(&machine)
                ),
            }
        }
    }
    assert!(built > 0, "no optimized fixture built a theorem");
}

/// The reviewed digest of `slice14_snapshots.smt2`.
const SLICE_FOURTEEN_SNAPSHOT_SHA256: &str =
    "d97feff3a9fd293b494ee5ba3ec43c5401804a32f1d988df4c88ac06f0ff52f1";

/// Every slice-14 fixture's theorem, as the replay renders it, is the
/// reviewed golden text, and does not depend on the function's name.
#[test]
fn slice_fourteen_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice14_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_FOURTEEN {
        let (source, machine) = slice14_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice14_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_FOURTEEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_FOURTEEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-14 snapshots drifted");
}
