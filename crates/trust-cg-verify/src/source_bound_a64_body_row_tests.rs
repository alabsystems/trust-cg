// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Row-by-row fixtures of the AArch64 whole-body owner.
//!
//! * Every admitted machine row and every admitted LIR opcode binds in at
//!   least one hand-built pair, and for every row but `RET` a body that is
//!   right only under a plausible mis-model of that row (a neighbouring row,
//!   another condition, another width, another shift kind or amount, another
//!   branch sense or bit) is refused by name. The census at the end fails if a
//!   row is admitted without both. This holds each row's word semantics against
//!   independently written LIR semantics; `trust-cg-codegen`
//!   `aarch64_source_bound_body` holds the same model against the host CPU.
//! * The condition table after `TST` (C and V clear) at both widths and in
//!   both operand forms.
//! * The reach gate of the shift-domain premise: a shift executed only on one
//!   arm constrains only the inputs that reach it.
//! * The verifier's Enforce rejection of a recognized wrong body.

use super::*;
use std::collections::BTreeSet;

fn iconst(ty: Type, imm: i64, result: u32) -> Instruction {
    ins(L::Iconst { ty, imm }, &[], &[result])
}

fn single(params: &[Type], ret_ty: Type, insts: Vec<Instruction>) -> Function {
    lir(params, ret_ty, vec![(vec![], insts)])
}

/// One block of `body` and `RET`.
fn rows(params: &[Type], ret_ty: Type, mut body: Vec<MachInst>) -> MachFunction {
    body.push(ret());
    machine(params, ret_ty, vec![(body, vec![])])
}

fn zr(width: u32) -> O {
    O::Special(if width == 32 {
        SpecialReg::WZR
    } else {
        SpecialReg::XZR
    })
}

fn ty_of_width(width: u32) -> Type {
    if width == 32 { Type::I32 } else { Type::I64 }
}

/// Register `n` at `width`.
fn r(width: u32, n: u16) -> O {
    if width == 32 { w(n) } else { x(n) }
}

/// One hand-built pair for the row `row`: `good` must bind; `wrong` (right
/// only under a mis-model of `row`) must be refused as a mismatch.
struct Fixture {
    row: &'static str,
    name: String,
    source: Function,
    good: MachFunction,
    wrong: Option<MachFunction>,
}

fn fixture(
    row: &'static str,
    name: impl Into<String>,
    source: Function,
    good: MachFunction,
    wrong: Option<MachFunction>,
) -> Fixture {
    Fixture {
        row,
        name: name.into(),
        source,
        good,
        wrong,
    }
}

/// `f(a, b) = a <op> (b <shift> k)`, the shifted-register sources.
fn shifted_source(width: u32, op: L, shift: Option<L>, k: i64) -> Function {
    let ty = ty_of_width(width);
    let mut insts = vec![iconst(ty.clone(), k, 10)];
    match shift {
        Some(shift) => insts.push(ins(shift, &[1, 10], &[11])),
        None => {
            // A rotate right by k: (b >> k) | (b << (width - k)).
            insts.push(ins(L::Ushr, &[1, 10], &[12]));
            insts.push(iconst(ty.clone(), i64::from(width) - k, 13));
            insts.push(ins(L::Ishl, &[1, 13], &[14]));
            insts.push(ins(L::Bor, &[12, 14], &[11]));
        }
    }
    insts.push(ins(op, &[0, 11], &[15]));
    insts.push(ins(L::Return, &[15], &[]));
    single(&[ty.clone(), ty.clone()], ty, insts)
}

/// `f(a) = a <op> c` with the constant `c`.
fn constant_source(width: u32, op: L, c: i64) -> Function {
    let ty = ty_of_width(width);
    single(
        std::slice::from_ref(&ty),
        ty.clone(),
        vec![
            iconst(ty.clone(), c, 10),
            ins(op, &[0, 10], &[11]),
            ins(L::Return, &[11], &[]),
        ],
    )
}

/// `f(a, b, x, y) = if a < b { x } else { g(y) }` (signed), `g` given by
/// `otherwise` (instructions defining value 11 from value 3).
fn select_source(width: u32, otherwise: Vec<Instruction>) -> Function {
    let ty = ty_of_width(width);
    let mut insts = vec![ins(
        L::Icmp {
            cond: IntCC::SignedLessThan,
        },
        &[0, 1],
        &[10],
    )];
    insts.extend(otherwise);
    insts.push(ins(
        L::Select {
            cond: IntCC::NotEqual,
        },
        &[10, 2, 11],
        &[12],
    ));
    insts.push(ins(L::Return, &[12], &[]));
    single(&vec![ty.clone(); 4], ty, insts)
}

fn select_body(width: u32, row: M) -> MachFunction {
    let ty = ty_of_width(width);
    rows(
        &vec![ty.clone(); 4],
        ty,
        vec![
            mi(M::CmpRR, vec![r(width, 0), r(width, 1)]),
            mi(row, vec![r(width, 0), r(width, 2), r(width, 3), imm(11)]),
        ],
    )
}

/// `f(t, x, y, b) = if cond { x ^ y } else { x - y }` written as a branching
/// CFG: `cond` is computed into value 10 by `test`; the then arm passes
/// `x ^ y`, the else arm `x - y`, as the join's block argument.
fn branching_source(test: Vec<Instruction>) -> Function {
    let mut entry = test;
    entry.push(ins(
        L::Brif {
            cond: Value(10),
            then_dest: Block(1),
            else_dest: Block(2),
        },
        &[10],
        &[],
    ));
    lir(
        &four_i64(),
        Type::I64,
        vec![
            (vec![], entry),
            (
                vec![],
                vec![
                    ins(L::Bxor, &[1, 2], &[20]),
                    ins(L::Copy, &[20], &[22]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Isub, &[1, 2], &[21]),
                    ins(L::Copy, &[21], &[22]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (vec![(22, Type::I64)], vec![ins(L::Return, &[22], &[])]),
        ],
    )
}

/// The diamond the branch rows are bound in: block 0 runs `test` and then
/// `branch` to block 2; block 1 (the fall-through) computes `x ^ y` (or
/// `x - y` when `taken_is_then`) and jumps to the join; block 2 computes the
/// other value and falls through to block 3, which returns.
fn branch_body(test: Vec<MachInst>, branch: MachInst, taken_is_then: bool) -> MachFunction {
    let eor = mi(M::EorRR, vec![x(0), x(1), x(2)]);
    let sub = mi(M::SubRR, vec![x(0), x(1), x(2)]);
    let (fall, taken) = if taken_is_then {
        (sub, eor)
    } else {
        (eor, sub)
    };
    let mut entry = test;
    entry.push(branch);
    machine(
        &four_i64(),
        Type::I64,
        vec![
            (entry, vec![2, 1]),
            (vec![fall, mi(M::B, vec![blk(3)])], vec![3]),
            (vec![taken], vec![3]),
            (vec![ret()], vec![]),
        ],
    )
}

/// The value 10 = `(a & mask) != 0`.
fn bit_test(mask: i64) -> Vec<Instruction> {
    vec![
        iconst(Type::I64, mask, 30),
        ins(L::Band, &[0, 30], &[31]),
        iconst(Type::I64, 0, 32),
        ins(
            L::Icmp {
                cond: IntCC::NotEqual,
            },
            &[31, 32],
            &[10],
        ),
    ]
}

/// Fixtures of the straight-line value rows at `width`.
fn value_fixtures(width: u32, out: &mut Vec<Fixture>) {
    let ty = ty_of_width(width);
    let two = vec![ty.clone(), ty.clone()];
    let reg = |n| r(width, n);
    // Three-register rows, each against a neighbour.
    for (row, op, opcode, neighbour) in [
        ("AddRR", L::Iadd, M::AddRR, M::SubRR),
        ("SubRR", L::Isub, M::SubRR, M::AddRR),
        ("AndRR", L::Band, M::AndRR, M::BicRR),
        ("OrrRR", L::Bor, M::OrrRR, M::OrnRR),
        ("EorRR", L::Bxor, M::EorRR, M::OrrRR),
        ("BicRR", L::BandNot, M::BicRR, M::AndRR),
        ("OrnRR", L::BorNot, M::OrnRR, M::OrrRR),
    ] {
        out.push(fixture(
            row,
            format!("{row}/w{width}"),
            int_binary(ty.clone(), op),
            binary_machine(ty.clone(), opcode),
            Some(binary_machine(ty.clone(), neighbour)),
        ));
    }
    // Register shifts by the masked amount, each against another kind.
    for (row, op, opcode, other) in [
        ("LslRR", L::Ishl, M::LslRR, M::LsrRR),
        ("LsrRR", L::Ushr, M::LsrRR, M::AsrRR),
        ("AsrRR", L::Sshr, M::AsrRR, M::LsrRR),
    ] {
        out.push(fixture(
            row,
            format!("{row}/w{width}"),
            shift(ty.clone(), op, true),
            binary_machine(ty.clone(), opcode),
            Some(binary_machine(ty.clone(), other)),
        ));
    }
    let one = |body: Vec<MachInst>| rows(std::slice::from_ref(&ty), ty.clone(), body);
    // imm12 rows.
    out.push(fixture(
        "AddRI",
        format!("AddRI/w{width}"),
        constant_source(width, L::Iadd, 7),
        one(vec![mi(M::AddRI, vec![reg(0), reg(0), imm(7)])]),
        Some(one(vec![mi(M::SubRI, vec![reg(0), reg(0), imm(7)])])),
    ));
    out.push(fixture(
        "SubRI",
        format!("SubRI/w{width}"),
        constant_source(width, L::Isub, 7),
        one(vec![mi(M::SubRI, vec![reg(0), reg(0), imm(7)])]),
        Some(one(vec![mi(M::AddRI, vec![reg(0), reg(0), imm(7)])])),
    ));
    out.push(fixture(
        "AddRIShift12",
        format!("AddRIShift12/w{width}"),
        constant_source(width, L::Iadd, 5 << 12),
        one(vec![mi(M::AddRIShift12, vec![reg(0), reg(0), imm(5)])]),
        Some(one(vec![mi(M::AddRI, vec![reg(0), reg(0), imm(5)])])),
    ));
    // Logical immediates, each against another mask or row.
    out.push(fixture(
        "AndRI",
        format!("AndRI/w{width}"),
        constant_source(width, L::Band, 0xff),
        one(vec![mi(M::AndRI, vec![reg(0), reg(0), imm(0xff)])]),
        Some(one(vec![mi(M::AndRI, vec![reg(0), reg(0), imm(0x7f)])])),
    ));
    out.push(fixture(
        "OrrRI",
        format!("OrrRI/w{width}"),
        constant_source(width, L::Bor, 0xff),
        one(vec![mi(M::OrrRI, vec![reg(0), reg(0), imm(0xff)])]),
        Some(one(vec![mi(M::OrrRI, vec![reg(0), reg(0), imm(0x7f)])])),
    ));
    out.push(fixture(
        "EorRI",
        format!("EorRI/w{width}"),
        constant_source(width, L::Bxor, 0xff),
        one(vec![mi(M::EorRI, vec![reg(0), reg(0), imm(0xff)])]),
        Some(one(vec![mi(M::OrrRI, vec![reg(0), reg(0), imm(0xff)])])),
    ));
    // NEG against NOT (ORN from the zero register).
    out.push(fixture(
        "Neg",
        format!("Neg/w{width}"),
        single(
            std::slice::from_ref(&ty),
            ty.clone(),
            vec![ins(L::Ineg, &[0], &[10]), ins(L::Return, &[10], &[])],
        ),
        one(vec![mi(M::Neg, vec![reg(0), reg(0)])]),
        Some(one(vec![mi(M::OrnRR, vec![reg(0), zr(width), reg(0)])])),
    ));
    // Immediate shifts and the bitfield moves, against another kind.
    let imm_shift = |op: L, k: i64| constant_source(width, op, k);
    let top = i64::from(width) - 1;
    for (row, op, k, good, wrong) in [
        (
            "LslRI",
            L::Ishl,
            3,
            mi(M::LslRI, vec![reg(0), reg(0), imm(3)]),
            mi(M::LsrRI, vec![reg(0), reg(0), imm(3)]),
        ),
        (
            "LsrRI",
            L::Ushr,
            7,
            mi(M::LsrRI, vec![reg(0), reg(0), imm(7)]),
            mi(M::AsrRI, vec![reg(0), reg(0), imm(7)]),
        ),
        (
            "AsrRI",
            L::Sshr,
            9,
            mi(M::AsrRI, vec![reg(0), reg(0), imm(9)]),
            mi(M::AsrRI, vec![reg(0), reg(0), imm(8)]),
        ),
        (
            "Ubfm",
            L::Ushr,
            7,
            mi(M::Ubfm, vec![reg(0), reg(0), imm(7), imm(top)]),
            mi(M::Sbfm, vec![reg(0), reg(0), imm(7), imm(top)]),
        ),
        (
            "Sbfm",
            L::Sshr,
            9,
            mi(M::Sbfm, vec![reg(0), reg(0), imm(9), imm(top)]),
            mi(M::Ubfm, vec![reg(0), reg(0), imm(9), imm(top)]),
        ),
    ] {
        out.push(fixture(
            row,
            format!("{row}/w{width}"),
            imm_shift(op, k),
            one(vec![good]),
            Some(one(vec![wrong])),
        ));
    }
    // Shifted-register rows, against the other shift kind (or, for the
    // rotate, the shift it is not).
    for (row, op, shift_op, k, opcode, other) in [
        (
            "AddRRShift",
            L::Iadd,
            Some(L::Ishl),
            3,
            M::AddRRShift,
            M::AddRRShiftLsr,
        ),
        (
            "SubRRShift",
            L::Isub,
            Some(L::Ishl),
            3,
            M::SubRRShift,
            M::AddRRShift,
        ),
        (
            "AddRRShiftLsr",
            L::Iadd,
            Some(L::Ushr),
            3,
            M::AddRRShiftLsr,
            M::AddRRShift,
        ),
        (
            "EorRRLsl",
            L::Bxor,
            Some(L::Ishl),
            7,
            M::EorRRLsl,
            M::EorRRLsr,
        ),
        (
            "EorRRLsr",
            L::Bxor,
            Some(L::Ushr),
            7,
            M::EorRRLsr,
            M::EorRRLsl,
        ),
        ("EorRRShift", L::Bxor, None, 7, M::EorRRShift, M::EorRRLsr),
    ] {
        let body = |opcode: M| {
            rows(
                &two,
                ty.clone(),
                vec![mi(opcode, vec![reg(0), reg(0), reg(1), imm(k)])],
            )
        };
        out.push(fixture(
            row,
            format!("{row}/w{width}"),
            shifted_source(width, op, shift_op, k),
            body(opcode),
            Some(body(other)),
        ));
    }
    // CSEL and its increment, invert and negate forms, against each other.
    let succ = vec![iconst(ty.clone(), 1, 13), ins(L::Iadd, &[3, 13], &[11])];
    for (row, otherwise, opcode, other) in [
        ("Csel", vec![ins(L::Copy, &[3], &[11])], M::Csel, M::Csinc),
        ("Csinc", succ, M::Csinc, M::Csel),
        ("Csinv", vec![ins(L::Bnot, &[3], &[11])], M::Csinv, M::Csneg),
        ("Csneg", vec![ins(L::Ineg, &[3], &[11])], M::Csneg, M::Csinv),
    ] {
        out.push(fixture(
            row,
            format!("{row}/w{width}"),
            select_source(width, otherwise),
            select_body(width, opcode),
            Some(select_body(width, other)),
        ));
    }
    // CMP (register and imm12) with CSET, against the opposite condition.
    let compare = single(
        &two,
        Type::B1,
        vec![
            ins(
                L::Icmp {
                    cond: IntCC::UnsignedLessThan,
                },
                &[0, 1],
                &[10],
            ),
            ins(L::Return, &[10], &[]),
        ],
    );
    let cset = |cc: i64| {
        rows(
            &two,
            Type::B1,
            vec![
                mi(M::CmpRR, vec![reg(0), reg(1)]),
                mi(M::CSet, vec![w(0), imm(cc)]),
            ],
        )
    };
    out.push(fixture(
        "CmpRR",
        format!("CmpRR/w{width}"),
        compare.clone(),
        cset(3),
        Some(cset(2)),
    ));
    out.push(fixture(
        "CSet",
        format!("CSet/w{width}"),
        compare,
        cset(3),
        Some(cset(11)),
    ));
    let below_seven = single(
        std::slice::from_ref(&ty),
        Type::B1,
        vec![
            iconst(ty.clone(), 7, 10),
            ins(
                L::Icmp {
                    cond: IntCC::UnsignedLessThan,
                },
                &[0, 10],
                &[11],
            ),
            ins(L::Return, &[11], &[]),
        ],
    );
    let cmp_imm = |value: i64| {
        rows(
            std::slice::from_ref(&ty),
            Type::B1,
            vec![
                mi(M::CmpRI, vec![reg(0), imm(value)]),
                mi(M::CSet, vec![w(0), imm(3)]),
            ],
        )
    };
    out.push(fixture(
        "CmpRI",
        format!("CmpRI/w{width}"),
        below_seven,
        cmp_imm(7),
        Some(cmp_imm(8)),
    ));
}

/// Fixtures of the extensions, the moves and the copies.
fn extension_and_move_fixtures(out: &mut Vec<Fixture>) {
    let i64_1 = [Type::I64];
    let i32_1 = [Type::I32];
    // UXTB/UXTH write W (zero-extended from 8/16 bits).
    for (row, mask, opcode, other) in [
        ("Uxtb", 0xff, M::Uxtb, M::Uxth),
        ("Uxth", 0xffff, M::Uxth, M::Uxtb),
    ] {
        out.push(fixture(
            row,
            row,
            constant_source(32, L::Band, mask),
            rows(&i32_1, Type::I32, vec![mi(opcode, vec![w(0), w(0)])]),
            Some(rows(&i32_1, Type::I32, vec![mi(other, vec![w(0), w(0)])])),
        ));
    }
    // UXTW (ORR Wd, WZR, Wn) against SXTW.
    out.push(fixture(
        "Uxtw",
        "Uxtw",
        constant_source(64, L::Band, 0xffff_ffff),
        rows(&i64_1, Type::I64, vec![mi(M::Uxtw, vec![x(0), x(0)])]),
        Some(rows(&i64_1, Type::I64, vec![mi(M::Sxtw, vec![x(0), x(0)])])),
    ));
    // SXTB/SXTH/SXTW (SBFM Xd): (a << (64 - n)) >> (64 - n), signed.
    for (row, bits, opcode, other) in [
        ("Sxtb", 8, M::Sxtb, M::Sxth),
        ("Sxth", 16, M::Sxth, M::Sxtb),
        ("Sxtw", 32, M::Sxtw, M::Uxtw),
    ] {
        let source = single(
            &i64_1,
            Type::I64,
            vec![
                iconst(Type::I64, 64 - bits, 10),
                ins(L::Ishl, &[0, 10], &[11]),
                ins(L::Sshr, &[11, 10], &[12]),
                ins(L::Return, &[12], &[]),
            ],
        );
        out.push(fixture(
            row,
            row,
            source,
            rows(&i64_1, Type::I64, vec![mi(opcode, vec![x(0), x(0)])]),
            Some(rows(&i64_1, Type::I64, vec![mi(other, vec![x(0), x(0)])])),
        ));
    }
    // Constants through a scratch register: MOVZ (both operand forms), MOVN,
    // MOVK at every halfword, MOVI.
    let with_constant = |width: u32, moves: Vec<MachInst>, op: M| {
        let ty = ty_of_width(width);
        let mut body = moves;
        body.push(mi(op, vec![r(width, 0), r(width, 0), r(width, 4)]));
        rows(std::slice::from_ref(&ty), ty.clone(), body)
    };
    out.push(fixture(
        "Movz",
        "Movz",
        constant_source(64, L::Iadd, 0x1234),
        with_constant(
            64,
            vec![mi(M::Movz, vec![x(4), imm(0x1234), imm(0)])],
            M::AddRR,
        ),
        Some(with_constant(
            64,
            vec![mi(M::Movz, vec![x(4), imm(0x1235)])],
            M::AddRR,
        )),
    ));
    for width in [32, 64] {
        out.push(fixture(
            "Movn",
            format!("Movn/w{width}"),
            constant_source(width, L::Iadd, !0x1234),
            with_constant(
                width,
                vec![mi(M::Movn, vec![r(width, 4), imm(0x1234)])],
                M::AddRR,
            ),
            Some(with_constant(
                width,
                vec![mi(M::Movz, vec![r(width, 4), imm(0x1234)])],
                M::AddRR,
            )),
        ));
    }
    out.push(fixture(
        "Movk",
        "Movk/w64",
        constant_source(64, L::Bxor, 0xabcd_0001_5678_1234_u64 as i64),
        with_constant(
            64,
            vec![
                mi(M::Movz, vec![x(4), imm(0x1234)]),
                mi(M::Movk, vec![x(4), imm(0x5678), imm(16)]),
                mi(M::Movk, vec![x(4), imm(0x0001), imm(32)]),
                mi(M::Movk, vec![x(4), imm(0xabcd), imm(48)]),
            ],
            M::EorRR,
        ),
        Some(with_constant(
            64,
            vec![
                mi(M::Movz, vec![x(4), imm(0x1234)]),
                mi(M::Movk, vec![x(4), imm(0x5678), imm(16)]),
                mi(M::Movk, vec![x(4), imm(0x0001), imm(16)]),
                mi(M::Movk, vec![x(4), imm(0xabcd), imm(48)]),
            ],
            M::EorRR,
        )),
    ));
    out.push(fixture(
        "Movk",
        "Movk/w32",
        constant_source(32, L::Bxor, 0x0005_1234),
        with_constant(
            32,
            vec![
                mi(M::Movz, vec![w(4), imm(0x1234)]),
                mi(M::Movk, vec![w(4), imm(5), imm(16)]),
            ],
            M::EorRR,
        ),
        // The two-operand MOVK replaces the low halfword.
        Some(with_constant(
            32,
            vec![
                mi(M::Movz, vec![w(4), imm(0x1234)]),
                mi(M::Movk, vec![w(4), imm(5)]),
            ],
            M::EorRR,
        )),
    ));
    out.push(fixture(
        "MovI",
        "MovI",
        constant_source(64, L::Iadd, 7),
        with_constant(64, vec![mi(M::MovI, vec![x(4), imm(7)])], M::AddRR),
        Some(with_constant(
            64,
            vec![mi(M::MovI, vec![x(4), imm(6)])],
            M::AddRR,
        )),
    ));
    // Copies. A W copy zeroes the upper half: `a + (b & 0xffff_ffff)` is a
    // W copy and an X add; the X copy is wrong for it, and the W copy is
    // wrong for `a + b`.
    let two = [Type::I64, Type::I64];
    let low_add = single(
        &two,
        Type::I64,
        vec![
            iconst(Type::I64, 0xffff_ffff, 10),
            ins(L::Band, &[1, 10], &[11]),
            ins(L::Iadd, &[0, 11], &[12]),
            ins(L::Return, &[12], &[]),
        ],
    );
    let wide_add = single(
        &two,
        Type::I64,
        vec![
            ins(L::Copy, &[1], &[10]),
            ins(L::Iadd, &[0, 10], &[11]),
            ins(L::Return, &[11], &[]),
        ],
    );
    let copy_add = |copy: MachInst| {
        rows(
            &two,
            Type::I64,
            vec![copy, mi(M::AddRR, vec![x(0), x(0), x(4)])],
        )
    };
    out.push(fixture(
        "MovR",
        "MovR/w32",
        low_add.clone(),
        copy_add(mi(M::MovR, vec![w(4), w(1)])),
        Some(copy_add(mi(M::MovR, vec![x(4), x(1)]))),
    ));
    out.push(fixture(
        "MovR",
        "MovR/w64",
        wide_add.clone(),
        copy_add(mi(M::MovR, vec![x(4), x(1)])),
        Some(copy_add(mi(M::MovR, vec![w(4), w(1)]))),
    ));
    // The typed copies fix their width whatever view the operands spell.
    out.push(fixture(
        "MOVWrr",
        "MOVWrr",
        low_add,
        copy_add(mi(M::MOVWrr, vec![x(4), x(1)])),
        Some(copy_add(mi(M::MOVXrr, vec![x(4), x(1)]))),
    ));
    out.push(fixture(
        "MOVXrr",
        "MOVXrr",
        wide_add,
        copy_add(mi(M::MOVXrr, vec![x(4), x(1)])),
        Some(copy_add(mi(M::MOVWrr, vec![x(4), x(1)]))),
    ));
}

/// Fixtures of the transfers: every conditional branch kind and sense in the
/// branch diamond against the opposite sense (or another bit, condition or
/// width), `B` against a jump to the wrong block, and the inert `NOP` and
/// `ALIGNNOP` counted as one word each by the displacement resolution.
fn transfer_fixtures(out: &mut Vec<Fixture>) {
    let less = vec![ins(
        L::Icmp {
            cond: IntCC::SignedLessThan,
        },
        &[0, 3],
        &[10],
    )];
    let cmp = || vec![mi(M::CmpRR, vec![x(0), x(3)])];
    // B.cond is taken when the source condition is false (to the else arm).
    out.push(fixture(
        "BCond",
        "BCond",
        branching_source(less.clone()),
        branch_body(cmp(), mi(M::BCond, vec![imm(10), blk(2)]), false),
        Some(branch_body(
            cmp(),
            mi(M::BCond, vec![imm(11), blk(2)]),
            false,
        )),
    ));
    let nonzero = bit_test(-1);
    out.push(fixture(
        "Cbz",
        "Cbz/w64",
        branching_source(nonzero.clone()),
        branch_body(vec![], mi(M::Cbz, vec![x(0), blk(2)]), false),
        Some(branch_body(vec![], mi(M::Cbnz, vec![x(0), blk(2)]), false)),
    ));
    out.push(fixture(
        "Cbnz",
        "Cbnz/w64",
        branching_source(nonzero),
        branch_body(vec![], mi(M::Cbnz, vec![x(0), blk(2)]), true),
        Some(branch_body(vec![], mi(M::Cbz, vec![x(0), blk(2)]), true)),
    ));
    // CBZ on the W view tests the low half only.
    out.push(fixture(
        "Cbz",
        "Cbz/w32",
        branching_source(bit_test(0xffff_ffff)),
        branch_body(vec![], mi(M::Cbz, vec![w(0), blk(2)]), false),
        Some(branch_body(vec![], mi(M::Cbz, vec![x(0), blk(2)]), false)),
    ));
    out.push(fixture(
        "Tbz",
        "Tbz/x3",
        branching_source(bit_test(8)),
        branch_body(vec![], mi(M::Tbz, vec![x(0), imm(3), blk(2)]), false),
        Some(branch_body(
            vec![],
            mi(M::Tbnz, vec![x(0), imm(3), blk(2)]),
            false,
        )),
    ));
    out.push(fixture(
        "Tbz",
        "Tbz/w31",
        branching_source(bit_test(0x8000_0000)),
        branch_body(vec![], mi(M::Tbz, vec![w(0), imm(31), blk(2)]), false),
        Some(branch_body(
            vec![],
            mi(M::Tbz, vec![w(0), imm(30), blk(2)]),
            false,
        )),
    ));
    out.push(fixture(
        "Tbnz",
        "Tbnz/x63",
        branching_source(bit_test(i64::MIN)),
        branch_body(vec![], mi(M::Tbnz, vec![x(0), imm(63), blk(2)]), true),
        Some(branch_body(
            vec![],
            mi(M::Tbnz, vec![x(0), imm(62), blk(2)]),
            true,
        )),
    ));
    // B to the join, against B back to the other arm's block (a CFG the
    // recorded successors do not name).
    let mut wrong_jump = branch_body(cmp(), mi(M::BCond, vec![imm(10), blk(2)]), false);
    wrong_jump.insts[3] = mi(M::B, vec![blk(2)]);
    out.push(fixture(
        "B",
        "B",
        branching_source(less.clone()),
        branch_body(cmp(), mi(M::BCond, vec![imm(10), blk(2)]), false),
        Some(wrong_jump),
    ));
    // Word displacements through the padding rows: block 0 = [CMP, B.cond]
    // (words 0-1), block 1 = [EOR, ALIGNNOP, B] (words 2-4), block 2 = [NOP,
    // SUB] (the pseudo NOP is no word; SUB is word 5), block 3 = [RET] (word
    // 6). The control of each row is the displacement that would be right
    // only if the row were counted the other way (ALIGNNOP as no word, NOP
    // as one): it lands off every block start.
    let padded = |to_else: i64, to_join: i64| {
        let mut body = machine(
            &four_i64(),
            Type::I64,
            vec![
                (
                    vec![
                        mi(M::CmpRR, vec![x(0), x(3)]),
                        mi(M::BCond, vec![imm(10), imm(to_else)]),
                    ],
                    vec![2, 1],
                ),
                (
                    vec![
                        mi(M::EorRR, vec![x(0), x(1), x(2)]),
                        mi(M::AlignNop, vec![]),
                        mi(M::B, vec![imm(to_join)]),
                    ],
                    vec![3],
                ),
                (
                    vec![mi(M::Nop, vec![]), mi(M::SubRR, vec![x(0), x(1), x(2)])],
                    vec![3],
                ),
                (vec![ret()], vec![]),
            ],
        );
        body.block_order = (0..4).map(BlockId).collect();
        body
    };
    for (row, wrong) in [("AlignNop", padded(3, 2)), ("Nop", padded(4, 3))] {
        out.push(fixture(
            row,
            row,
            branching_source(less.clone()),
            padded(4, 2),
            Some(wrong),
        ));
    }
}

/// The value 10 = what each condition code means after `TST` of `r` (value
/// 20): N is the sign of `r`, Z is `r == 0`, and C and V are clear.
fn after_tst(cc: u8, ty: &Type) -> Vec<Instruction> {
    let zero = iconst(ty.clone(), 0, 21);
    let against_zero = |cond: IntCC| vec![zero.clone(), ins(L::Icmp { cond }, &[20, 21], &[10])];
    match cc {
        0 => against_zero(IntCC::Equal),
        1 => against_zero(IntCC::NotEqual),
        4 | 11 => against_zero(IntCC::SignedLessThan),
        5 | 10 => against_zero(IntCC::SignedGreaterThanOrEqual),
        12 => against_zero(IntCC::SignedGreaterThan),
        13 => against_zero(IntCC::SignedLessThanOrEqual),
        // HS, VS, HI: C or V set (never after TST).
        2 | 6 | 8 => vec![iconst(Type::B1, 0, 10)],
        // LO, VC, LS, AL, NV.
        _ => vec![iconst(Type::B1, 1, 10)],
    }
}

/// `TST a, b` (or `TST a, #0xff`) then `CSEL x, y, cc`, for every condition
/// at both widths, against the opposite condition.
fn tst_fixtures(out: &mut Vec<Fixture>) {
    for width in [32u32, 64] {
        let ty = ty_of_width(width);
        for immediate in [false, true] {
            for cc in 0u8..16 {
                let mut insts = Vec::new();
                if immediate {
                    insts.push(iconst(ty.clone(), 0xff, 22));
                    insts.push(ins(L::Band, &[0, 22], &[20]));
                } else {
                    insts.push(ins(L::Band, &[0, 1], &[20]));
                }
                insts.extend(after_tst(cc, &ty));
                insts.push(ins(
                    L::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[10, 2, 3],
                    &[12],
                ));
                insts.push(ins(L::Return, &[12], &[]));
                let source = single(&vec![ty.clone(); 4], ty.clone(), insts);
                let body = |cc: u8| {
                    let tested = if immediate { imm(0xff) } else { r(width, 1) };
                    rows(
                        &vec![ty.clone(); 4],
                        ty.clone(),
                        vec![
                            mi(M::Tst, vec![r(width, 0), tested]),
                            mi(
                                M::Csel,
                                vec![r(width, 0), r(width, 2), r(width, 3), imm(i64::from(cc))],
                            ),
                        ],
                    )
                };
                // AL and NV both always hold: neither is the other's opposite.
                let wrong = (cc < 14).then(|| body(cc ^ 1));
                out.push(fixture(
                    "Tst",
                    format!(
                        "Tst/w{width}/{}/cc{cc}",
                        if immediate { "imm" } else { "reg" }
                    ),
                    source,
                    body(cc),
                    wrong,
                ));
            }
        }
    }
}

fn all_fixtures() -> Vec<Fixture> {
    let mut out = Vec::new();
    value_fixtures(32, &mut out);
    value_fixtures(64, &mut out);
    extension_and_move_fixtures(&mut out);
    transfer_fixtures(&mut out);
    tst_fixtures(&mut out);
    out.push(fixture(
        "Uxtb",
        "Uxtb/narrow-source-to-word",
        single(
            &[Type::I8],
            Type::I32,
            vec![
                ins(
                    L::Uextend {
                        from_ty: Type::I8,
                        to_ty: Type::I32,
                    },
                    &[0],
                    &[1],
                ),
                ins(L::Return, &[1], &[]),
            ],
        ),
        rows(&[Type::I8], Type::I32, vec![mi(M::Uxtb, vec![w(0), w(0)])]),
        Some(rows(
            &[Type::I8],
            Type::I32,
            vec![mi(M::Sxtb, vec![w(0), w(0)])],
        )),
    ));
    out
}

#[test]
fn every_admitted_row_and_lir_opcode_binds_and_its_mis_model_is_refuted() {
    let fixtures = all_fixtures();
    let mut bound_rows: BTreeSet<String> = BTreeSet::new();
    let mut controlled: BTreeSet<&str> = BTreeSet::new();
    let mut lir_opcodes: BTreeSet<String> = BTreeSet::new();
    for fixture in &fixtures {
        let owner = match source_bound_a64_body(&fixture.source, &fixture.good) {
            Ok(owner) => owner,
            Err(refusal) => panic!("{}: expected a bound body, got {refusal}", fixture.name),
        };
        // The row under test is in the body and, unless it is a copy or
        // constant (stated, uncredited) or inert, in the credited slice.
        let rows_of = |opcode: &str| -> Vec<InstId> {
            fixture
                .good
                .insts
                .iter()
                .enumerate()
                .filter(|(_, inst)| format!("{:?}", inst.opcode) == opcode)
                .map(|(i, _)| InstId(i as u32))
                .collect()
        };
        let under_test = rows_of(fixture.row);
        assert!(
            !under_test.is_empty(),
            "{}: no {} row",
            fixture.name,
            fixture.row
        );
        // Padding carries no value, and a condition that reads only C or V
        // (or none) does not read the flags `TST` defines as values.
        let value_free = matches!(fixture.row, "Nop" | "AlignNop")
            || (fixture.row == "Tst"
                && ["cc2", "cc3", "cc6", "cc7", "cc14", "cc15"]
                    .iter()
                    .any(|cc| fixture.name.ends_with(cc)));
        if !value_free {
            assert!(
                under_test.iter().all(|id| owner.covers(*id)),
                "{}: {} is outside the theorem's slice",
                fixture.name,
                fixture.row
            );
        }
        for inst in &fixture.good.insts {
            bound_rows.insert(format!("{:?}", inst.opcode));
        }
        for block in fixture.source.blocks.values() {
            for inst in &block.instructions {
                lir_opcodes.insert(source::opcode_name(&inst.opcode));
            }
        }
        if let Some(wrong) = &fixture.wrong {
            match source_bound_a64_body(&fixture.source, wrong) {
                Err(A64BodyRefusal::Mismatch(_)) => {
                    controlled.insert(fixture.row);
                }
                Err(other) => panic!(
                    "{}: the mis-modelled body is refused without a mismatch: {other}",
                    fixture.name
                ),
                Ok(_) => panic!("{}: the mis-modelled body binds", fixture.name),
            }
        }
    }
    for name in ADMITTED_MACHINE_OPCODES {
        assert!(bound_rows.contains(*name), "no fixture binds {name}");
        assert!(
            *name == "Ret" || controlled.contains(name),
            "no mis-model control refutes {name}"
        );
    }
    for name in ADMITTED_LIR_OPCODES {
        assert!(lir_opcodes.contains(*name), "no fixture source uses {name}");
    }
    println!(
        "A64_BODY_ROW_FIXTURES fixtures={} rows={} controlled={} lir_opcodes={}",
        fixtures.len(),
        bound_rows.len(),
        controlled.len(),
        lir_opcodes.len()
    );
}

/// The name-to-value environment of an obligation at the given inputs (every
/// other input zero): its definitions, in definition order, then its domain
/// premise (`None` when it has none).
fn evaluate(obligation: &ProofObligation, inputs: &[(&str, u64)]) -> (Option<bool>, u64, u64) {
    let mut env: HashMap<String, u64> = obligation
        .inputs
        .iter()
        .map(|(name, _)| (name.clone(), 0))
        .collect();
    for (name, value) in inputs {
        env.insert((*name).to_owned(), *value);
    }
    let mut domain = None;
    for premise in obligation.preconditions.iter().rev() {
        match premise {
            E::Eq { lhs, rhs } if matches!(lhs.as_ref(), E::Var { .. }) => {
                let E::Var { name, .. } = lhs.as_ref() else {
                    unreachable!()
                };
                let value = eval(rhs, &env);
                env.insert(name.clone(), value);
            }
            other => {
                assert!(domain.is_none(), "one domain premise");
                domain = Some(eval(other, &env) == 1);
            }
        }
    }
    (
        domain,
        eval(&obligation.trust_ir_expr, &env),
        eval(&obligation.aarch64_expr, &env),
    )
}

/// `if c { x << y } else { z }`: the shift's domain constraint holds only on
/// inputs that reach it.
fn arm_shift() -> Function {
    lir(
        &[Type::B1, Type::I64, Type::I64, Type::I64],
        Type::I64,
        vec![
            (
                vec![],
                vec![ins(
                    L::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    &[0],
                    &[],
                )],
            ),
            (
                vec![],
                vec![
                    ins(L::Ishl, &[1, 2], &[10]),
                    ins(L::Copy, &[10], &[20]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (
                vec![],
                vec![
                    ins(L::Copy, &[3], &[20]),
                    ins(L::Jump { dest: Block(3) }, &[], &[]),
                ],
            ),
            (vec![(20, Type::I64)], vec![ins(L::Return, &[20], &[])]),
        ],
    )
}

/// TBZ on the Boolean's bit to the else arm; `else_rows` compute the else
/// arm's X0.
fn arm_shift_machine(else_rows: Vec<MachInst>) -> MachFunction {
    let mut function = machine(
        &[Type::B1, Type::I64, Type::I64, Type::I64],
        Type::I64,
        vec![
            (vec![mi(M::Tbz, vec![x(0), imm(0), blk(2)])], vec![2, 1]),
            (
                vec![mi(M::LslRR, vec![x(0), x(1), x(2)]), mi(M::B, vec![blk(3)])],
                vec![3],
            ),
            (else_rows, vec![3]),
            (vec![ret()], vec![]),
        ],
    );
    function.block_order = (0..4).map(BlockId).collect();
    function
}

#[test]
fn the_shift_domain_premise_is_gated_by_the_shift_block_reach() {
    let source = arm_shift();
    let good = arm_shift_machine(vec![mi(M::MOVXrr, vec![x(0), x(3)])]);
    let owner = bind(&source, &good);
    let obligation = owner.obligation();
    let at = |c: u64, y: u64| {
        evaluate(
            obligation,
            &[("e0", c), ("e1", 0x1234), ("e2", y), ("e3", 0x99)],
        )
    };
    // Not taken: the shift is not executed, so every amount is in the domain.
    assert_eq!(at(0, 64).0, Some(true));
    assert_eq!(at(0, u64::MAX).0, Some(true));
    // Taken: only amounts below the width are.
    assert_eq!(at(1, 64).0, Some(false));
    assert_eq!(at(1, 63).0, Some(true));
    // A body that is wrong only where the shift is not executed and its
    // amount is out of range: X0 = y < 64 ? z : x on the else arm. The
    // concrete check refutes it, and the theorem itself has a counterexample
    // inside its domain.
    let wrong = arm_shift_machine(vec![
        mi(M::CmpRI, vec![x(2), imm(64)]),
        mi(M::Csel, vec![x(0), x(3), x(1), imm(3)]),
    ]);
    assert_return_mismatch(&source, &wrong);
    let theorem = diagnostic_a64_body_obligation(&source, &wrong).unwrap();
    let (domain, source_value, machine_value) = evaluate(
        &theorem,
        &[("e0", 0), ("e1", 0x1234), ("e2", 64), ("e3", 0x99)],
    );
    assert_eq!(domain, Some(true));
    assert_eq!((source_value, machine_value), (0x99, 0x1234));
}

#[test]
fn enforce_rejects_a_recognized_wrong_body_by_name() {
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::{FunctionVerificationPreconditionFailure, FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let source = bool_pair(L::Band);
        // The correct body is classified, not rejected; without a replayed
        // proof nothing is credited.
        let good = bool_pair_machine(M::AndRR);
        let report = verifier.verify_with_lir_source_and_mode(
            &good,
            Some(&source),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(report.precondition_failure.is_none(), "{report:?}");
        assert_eq!(report.formally_credited_count(), 0);
        let preserved = machine(
            &[Type::B1, Type::B1],
            Type::B1,
            vec![(
                vec![
                    mi(M::Uxtb, vec![x(2), x(0)]),
                    mi(M::Uxtb, vec![x(19), x(1)]),
                    mi(M::AndRR, vec![x(0), x(2), x(19)]),
                    ret(),
                ],
                vec![],
            )],
        );
        for (wrong, expected) in [
            (bool_pair_machine(M::OrrRR), "returns a different value"),
            (preserved, "which the caller observes unchanged"),
        ] {
            let report = verifier.verify_with_lir_source_and_mode(
                &wrong,
                Some(&source),
                ProvenanceXCheckMode::Enforce,
            );
            let Some(FunctionVerificationPreconditionFailure::SourceBoundA64BodyMismatch(mismatch)) =
                &report.precondition_failure
            else {
                panic!("{:?}", report.precondition_failure)
            };
            assert!(mismatch.to_string().contains(expected), "{mismatch}");
            assert!(report.instructions.is_empty());
            assert!(report.has_failures());
            let text = report.precondition_failure.as_ref().unwrap().to_string();
            assert!(
                text.starts_with("[TCG-SOURCE-BOUND-A64-BODY-MISMATCH]"),
                "{text}"
            );
            let inventory = report.emitted_opcode_inventory();
            assert!(!inventory.is_promotable());
            assert!(
                inventory
                    .promotion_rejection_reason()
                    .unwrap()
                    .contains("[TCG-SOURCE-BOUND-A64-BODY-MISMATCH]")
            );
            // Warn reports but never rejects or credits; Off does not
            // classify.
            for mode in [ProvenanceXCheckMode::Warn, ProvenanceXCheckMode::Off] {
                let report = verifier.verify_with_lir_source_and_mode(&wrong, Some(&source), mode);
                assert!(report.precondition_failure.is_none(), "{mode:?}");
                assert_eq!(report.formally_credited_count(), 0, "{mode:?}");
            }
        }
    });
}
