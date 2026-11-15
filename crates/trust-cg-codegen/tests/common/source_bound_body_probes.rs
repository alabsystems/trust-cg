// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Hand-built probe bodies over every row the AArch64 whole-body owner admits
//! (`trust_cg_verify::source_bound_a64_body::ADMITTED_MACHINE_OPCODES`), for
//! the silicon differential of its machine model in `aarch64_source_bound_body`.
//!
//! Every probe is a frameless `(u64, u64, u64, u64) -> u64` body (X0-X3 in,
//! X0 out, observed whole) the owner's walk accepts: straight-line rows, or a
//! diamond whose branch rows carry the word displacements the encoder takes
//! (resolved here by the walk's own rule: one word per non-pseudo row). Each
//! probe names the row it is for and carries decoys: the same body with that
//! row replaced by a plausible mis-model of it (a neighbouring row, another
//! condition, width, shift kind or amount, branch sense or bit, or a padding
//! row counted the other way).
#![allow(dead_code)]

use trust_cg_ir::function::{MachBlock, Signature, Type};
use trust_cg_ir::regs::{PReg, SpecialReg};
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachInst, MachOperand as O};

/// Blocks of rows with their successors; a branch target is `O::Block` until
/// [`assemble`] resolves it.
pub type Blocks = Vec<(Vec<MachInst>, Vec<u32>)>;

pub struct Probe {
    /// The admitted row this probe is for.
    pub row: &'static str,
    pub name: String,
    pub function: MachFunction,
    /// Mis-models of `row`, each a complete body.
    pub decoys: Vec<(String, MachFunction)>,
}

/// The function of `blocks` in layout order, with every `O::Block` target
/// replaced by its word displacement (one word per non-pseudo row) and the
/// recorded predecessors derived from the successors.
pub fn assemble(name: &str, blocks: Blocks) -> MachFunction {
    let mut function = MachFunction::new(
        name.to_owned(),
        Signature::new(vec![Type::I64; 4], vec![Type::I64]),
    );
    function.insts.clear();
    function.blocks.clear();
    let count = blocks.len();
    let mut preds = vec![Vec::new(); count];
    let mut block_word = vec![0i64; count];
    let mut inst_word = Vec::new();
    let mut word = 0i64;
    for (index, (insts, succs)) in blocks.iter().enumerate() {
        for succ in succs {
            preds[*succ as usize].push(BlockId(index as u32));
        }
        block_word[index] = word;
        for inst in insts {
            inst_word.push(word);
            word += i64::from(!inst.is_pseudo());
        }
    }
    let mut position = 0;
    for (index, (insts, succs)) in blocks.into_iter().enumerate() {
        let mut ids = Vec::new();
        for mut inst in insts {
            for operand in &mut inst.operands {
                if let O::Block(target) = operand {
                    *operand = O::Imm(block_word[target.0 as usize] - inst_word[position]);
                }
            }
            ids.push(InstId(function.insts.len() as u32));
            function.insts.push(inst);
            position += 1;
        }
        function.blocks.push(MachBlock {
            insts: ids,
            preds: preds[index].clone(),
            succs: succs.into_iter().map(BlockId).collect(),
            loop_depth: 0,
        });
    }
    function.entry = BlockId(0);
    function.block_order = (0..count as u32).map(BlockId).collect();
    function
}

fn x(n: u16) -> O {
    O::PReg(PReg::new(n))
}

fn w(n: u16) -> O {
    O::PReg(PReg::new(32 + n))
}

fn r(width: u32, n: u16) -> O {
    if width == 32 { w(n) } else { x(n) }
}

fn zr(width: u32) -> O {
    O::Special(if width == 32 {
        SpecialReg::WZR
    } else {
        SpecialReg::XZR
    })
}

fn imm(value: i64) -> O {
    O::Imm(value)
}

fn blk(n: u32) -> O {
    O::Block(BlockId(n))
}

fn mi(opcode: M, operands: Vec<O>) -> MachInst {
    MachInst::new(opcode, operands)
}

/// `RET` through X30, using X0 (the result) as the ABI requires.
fn ret() -> MachInst {
    const RESULT: &[PReg] = &[trust_cg_ir::regs::X0];
    mi(M::Ret, vec![x(30)]).with_implicit_uses(RESULT)
}

/// One block: `rows` then `RET`.
fn straight(mut rows: Vec<MachInst>) -> Blocks {
    rows.push(ret());
    vec![(rows, vec![])]
}

/// Block 0 runs `entry` and `branch` (to block 2); block 1 computes
/// `x2 ^ x3` and jumps to block 3; block 2 computes `x2 - x3` and falls
/// through; block 3 returns.
fn diamond(entry: Vec<MachInst>, branch: MachInst) -> Blocks {
    let mut first = entry;
    first.push(branch);
    vec![
        (first, vec![2, 1]),
        (
            vec![mi(M::EorRR, vec![x(0), x(2), x(3)]), mi(M::B, vec![blk(3)])],
            vec![3],
        ),
        (vec![mi(M::SubRR, vec![x(0), x(2), x(3)])], vec![3]),
        (vec![ret()], vec![]),
    ]
}

struct Corpus(Vec<Probe>);

impl Corpus {
    fn push(
        &mut self,
        row: &'static str,
        name: String,
        blocks: Blocks,
        decoys: Vec<(String, Blocks)>,
    ) {
        let symbol = format!("probe_{}", self.0.len());
        self.0.push(Probe {
            row,
            name,
            function: assemble(&symbol, blocks),
            decoys: decoys
                .into_iter()
                .map(|(name, blocks)| (name, assemble(&symbol, blocks)))
                .collect(),
        });
    }

    /// A straight-line probe of `rows` whose decoys replace the row at
    /// `index` by each of `others`.
    fn line(
        &mut self,
        row: &'static str,
        name: String,
        rows: Vec<MachInst>,
        index: usize,
        others: Vec<MachInst>,
    ) {
        let decoys = others
            .into_iter()
            .map(|other| {
                let mut changed = rows.clone();
                let label = format!("{:?} {:?}", other.opcode, other.operands);
                changed[index] = other;
                (label, straight(changed))
            })
            .collect();
        self.push(row, name, straight(rows), decoys);
    }
}

fn value_probes(width: u32, corpus: &mut Corpus) {
    let reg = |n| r(width, n);
    for (row, opcode, neighbour) in [
        ("AddRR", M::AddRR, M::SubRR),
        ("SubRR", M::SubRR, M::AddRR),
        ("AndRR", M::AndRR, M::BicRR),
        ("OrrRR", M::OrrRR, M::OrnRR),
        ("EorRR", M::EorRR, M::OrrRR),
        ("BicRR", M::BicRR, M::AndRR),
        ("OrnRR", M::OrnRR, M::OrrRR),
        ("LslRR", M::LslRR, M::LsrRR),
        ("LsrRR", M::LsrRR, M::AsrRR),
        ("AsrRR", M::AsrRR, M::LsrRR),
    ] {
        let mut others = vec![mi(neighbour, vec![reg(0), reg(0), reg(1)])];
        if width == 32 {
            // The X-width row: a W write zeroes the upper half, and a W
            // shift takes its amount modulo 32.
            others.push(mi(opcode, vec![x(0), x(0), x(1)]));
        }
        corpus.line(
            row,
            format!("{row}/w{width}"),
            vec![mi(opcode, vec![reg(0), reg(0), reg(1)])],
            0,
            others,
        );
    }
    for value in [1, 0x123, 0xfff] {
        for (row, opcode, other) in [
            ("AddRI", M::AddRI, M::SubRI),
            ("SubRI", M::SubRI, M::AddRI),
            ("AddRIShift12", M::AddRIShift12, M::AddRI),
        ] {
            corpus.line(
                row,
                format!("{row}/w{width}/#{value:#x}"),
                vec![mi(opcode, vec![reg(0), reg(1), imm(value)])],
                0,
                vec![mi(other, vec![reg(0), reg(1), imm(value)])],
            );
        }
    }
    corpus.line(
        "Neg",
        format!("Neg/w{width}"),
        vec![mi(M::Neg, vec![reg(0), reg(1)])],
        0,
        vec![mi(M::OrnRR, vec![reg(0), zr(width), reg(1)])],
    );
    let masks: &[i64] = if width == 64 {
        &[
            0xff,
            0xf0f0_f0f0_f0f0_f0f0_u64 as i64,
            0x7fff_ffff_ffff_fffe,
            0x0000_ffff_0000_ffff,
            0x8000_0000_0000_00ff_u64 as i64,
        ]
    } else {
        &[0xff, 0xf0f0_f0f0, 0x7fff_fffe, 0x00ff_00ff, 0x8000_00ff]
    };
    for &mask in masks {
        for (row, opcode, other) in [
            ("AndRI", M::AndRI, M::OrrRI),
            ("OrrRI", M::OrrRI, M::EorRI),
            ("EorRI", M::EorRI, M::AndRI),
        ] {
            corpus.line(
                row,
                format!("{row}/w{width}/#{mask:#x}"),
                vec![mi(opcode, vec![reg(0), reg(1), imm(mask)])],
                0,
                vec![mi(other, vec![reg(0), reg(1), imm(mask)])],
            );
        }
    }
    let top = i64::from(width) - 1;
    for amount in [1, 7, top] {
        let near = if amount == top {
            amount - 1
        } else {
            amount + 1
        };
        for (row, opcode, other) in [
            ("LslRI", M::LslRI, M::LsrRI),
            ("LsrRI", M::LsrRI, M::AsrRI),
            ("AsrRI", M::AsrRI, M::LsrRI),
        ] {
            corpus.line(
                row,
                format!("{row}/w{width}/#{amount}"),
                vec![mi(opcode, vec![reg(0), reg(1), imm(amount)])],
                0,
                vec![
                    mi(other, vec![reg(0), reg(1), imm(amount)]),
                    mi(opcode, vec![reg(0), reg(1), imm(near)]),
                ],
            );
        }
    }
    let pairs: &[(i64, i64)] = if width == 64 {
        &[
            (0, 7),
            (7, 63),
            (60, 3),
            (4, 11),
            (63, 61),
            (40, 31),
            (2, 0),
            (0, 31),
        ]
    } else {
        &[(0, 7), (7, 31), (28, 3), (4, 11), (31, 29), (2, 0), (0, 15)]
    };
    // Each field ends below the register's top bit, where UBFM and SBFM
    // differ (a field that reaches it is the same under both).
    for &(immr, imms) in pairs {
        for (row, opcode, other) in [("Ubfm", M::Ubfm, M::Sbfm), ("Sbfm", M::Sbfm, M::Ubfm)] {
            corpus.line(
                row,
                format!("{row}/w{width}/#{immr},#{imms}"),
                vec![mi(opcode, vec![reg(0), reg(1), imm(immr), imm(imms)])],
                0,
                vec![mi(other, vec![reg(0), reg(1), imm(immr), imm(imms)])],
            );
        }
    }
    for amount in [1, 7, top] {
        let near = if amount == top {
            amount - 1
        } else {
            amount + 1
        };
        for (row, opcode, other) in [
            ("AddRRShift", M::AddRRShift, M::AddRRShiftLsr),
            ("SubRRShift", M::SubRRShift, M::AddRRShift),
            ("AddRRShiftLsr", M::AddRRShiftLsr, M::AddRRShift),
            ("EorRRLsl", M::EorRRLsl, M::EorRRLsr),
            ("EorRRLsr", M::EorRRLsr, M::EorRRLsl),
            ("EorRRShift", M::EorRRShift, M::EorRRLsr),
        ] {
            let mut others = vec![mi(opcode, vec![reg(0), reg(1), reg(2), imm(near)])];
            // Adding or subtracting `m << (width - 1)` is the same value (it is
            // 0 or the sign bit), so ADD is no decoy for SUB there.
            if !(opcode == M::SubRRShift && amount == top) {
                others.push(mi(other, vec![reg(0), reg(1), reg(2), imm(amount)]));
            }
            corpus.line(
                row,
                format!("{row}/w{width}/#{amount}"),
                vec![mi(opcode, vec![reg(0), reg(1), reg(2), imm(amount)])],
                0,
                others,
            );
        }
    }
    // Conditions: CMP (register and imm12) then CSET; TST (register and
    // logical immediate) then CSEL; CMP then each conditional select.
    let sign_and_low: i64 = if width == 64 {
        0x8000_0000_0000_00ff_u64 as i64
    } else {
        0x8000_00ff
    };
    for cc in 0i64..16 {
        let opposite = cc ^ 1;
        if cc < 14 {
            corpus.line(
                "CmpRR",
                format!("CmpRR+CSet/w{width}/cc{cc}"),
                vec![
                    mi(M::CmpRR, vec![reg(0), reg(1)]),
                    mi(M::CSet, vec![reg(0), imm(cc)]),
                ],
                1,
                vec![mi(M::CSet, vec![reg(0), imm(opposite)])],
            );
            corpus.line(
                "CSet",
                format!("CSet/w{width}/cc{cc}"),
                vec![
                    mi(M::CmpRR, vec![reg(1), reg(0)]),
                    mi(M::CSet, vec![x(0), imm(cc)]),
                ],
                1,
                vec![mi(M::CSet, vec![x(0), imm(opposite)])],
            );
            for value in [0, 0x7f, 0xfff] {
                corpus.line(
                    "CmpRI",
                    format!("CmpRI+CSet/w{width}/#{value:#x}/cc{cc}"),
                    vec![
                        mi(M::CmpRI, vec![reg(0), imm(value)]),
                        mi(M::CSet, vec![w(0), imm(cc)]),
                    ],
                    1,
                    vec![mi(M::CSet, vec![w(0), imm(opposite)])],
                );
            }
        }
        for tested in [reg(1), imm(sign_and_low)] {
            let form = if matches!(tested, O::Imm(_)) {
                "imm"
            } else {
                "reg"
            };
            let select = |cc| mi(M::Csel, vec![reg(0), reg(2), reg(3), imm(cc)]);
            corpus.line(
                "Tst",
                format!("Tst+CSel/w{width}/{form}/cc{cc}"),
                vec![mi(M::Tst, vec![reg(0), tested.clone()]), select(cc)],
                1,
                if cc < 14 {
                    vec![select(opposite)]
                } else {
                    vec![]
                },
            );
        }
        for (row, opcode, neighbour) in [
            ("Csel", M::Csel, M::Csinc),
            ("Csinc", M::Csinc, M::Csel),
            ("Csinv", M::Csinv, M::Csneg),
            ("Csneg", M::Csneg, M::Csinv),
        ] {
            let select = |opcode, cc| mi(opcode, vec![reg(0), reg(2), reg(3), imm(cc)]);
            // AL and NV always select the first operand: no decoy there.
            let others = if cc < 14 {
                vec![select(neighbour, cc), select(opcode, opposite)]
            } else {
                vec![]
            };
            corpus.line(
                row,
                format!("{row}/w{width}/cc{cc}"),
                vec![mi(M::CmpRR, vec![reg(0), reg(1)]), select(opcode, cc)],
                1,
                others,
            );
        }
    }
    // Moves.
    corpus.line(
        "Movz",
        format!("Movz/w{width}"),
        vec![mi(M::Movz, vec![reg(0), imm(0x1234)])],
        0,
        vec![mi(M::Movn, vec![reg(0), imm(0x1234)])],
    );
    corpus.line(
        "Movz",
        format!("Movz/w{width}/lsl0"),
        vec![mi(M::Movz, vec![reg(0), imm(0xbeef), imm(0)])],
        0,
        vec![mi(M::Movn, vec![reg(0), imm(0xbeef), imm(0)])],
    );
    corpus.line(
        "Movn",
        format!("Movn/w{width}"),
        vec![mi(M::Movn, vec![reg(0), imm(0x1234)])],
        0,
        vec![mi(M::Movz, vec![reg(0), imm(0x1234)])],
    );
    let shifts: &[i64] = if width == 64 {
        &[0, 16, 32, 48]
    } else {
        &[0, 16]
    };
    for &shift in shifts {
        let other = if shift == 0 { 16 } else { shift - 16 };
        corpus.line(
            "Movk",
            format!("Movk/w{width}/lsl{shift}"),
            vec![
                mi(M::MovR, vec![reg(0), reg(1)]),
                mi(M::Movk, vec![reg(0), imm(0xabcd), imm(shift)]),
            ],
            1,
            vec![mi(M::Movk, vec![reg(0), imm(0xabcd), imm(other)])],
        );
    }
    corpus.line(
        "Movk",
        format!("Movk/w{width}/two-operand"),
        vec![
            mi(M::MovR, vec![reg(0), reg(1)]),
            mi(M::Movk, vec![reg(0), imm(0x5a5a)]),
        ],
        1,
        vec![mi(M::Movk, vec![reg(0), imm(0x5a5a), imm(16)])],
    );
    corpus.line(
        "MovI",
        format!("MovI/w{width}"),
        vec![mi(M::MovI, vec![reg(0), imm(0x7fff)])],
        0,
        vec![mi(M::MovI, vec![reg(0), imm(0x7ffe)])],
    );
    corpus.line(
        "MovR",
        format!("MovR/w{width}"),
        vec![mi(M::MovR, vec![reg(0), reg(1)])],
        0,
        vec![if width == 32 {
            mi(M::MovR, vec![x(0), x(1)])
        } else {
            mi(M::MovR, vec![w(0), w(1)])
        }],
    );
}

fn extension_and_copy_probes(corpus: &mut Corpus) {
    // The encoder fixes each extension's width whatever view the operands
    // spell (UXTB/UXTH write W, UXTW is ORR Wd, WZR, Wn, SXTB/SXTH/SXTW write
    // X); both spellings are probed.
    for (row, opcode, other) in [
        ("Uxtb", M::Uxtb, M::Sxtb),
        ("Uxth", M::Uxth, M::Sxth),
        ("Uxtw", M::Uxtw, M::Sxtw),
        ("Sxtb", M::Sxtb, M::Uxtb),
        ("Sxth", M::Sxth, M::Uxth),
        ("Sxtw", M::Sxtw, M::Uxtw),
    ] {
        for (view, d, n) in [("w", w(0), w(1)), ("x", x(0), x(1))] {
            corpus.line(
                row,
                format!("{row}/{view}"),
                vec![mi(opcode, vec![d.clone(), n.clone()])],
                0,
                vec![mi(other, vec![d.clone(), n.clone()])],
            );
        }
    }
    for (row, opcode, other) in [
        ("MOVWrr", M::MOVWrr, M::MOVXrr),
        ("MOVXrr", M::MOVXrr, M::MOVWrr),
    ] {
        corpus.line(
            row,
            row.to_owned(),
            vec![mi(opcode, vec![x(0), x(1)])],
            0,
            vec![mi(other, vec![x(0), x(1)])],
        );
    }
}

fn control_probes(corpus: &mut Corpus) {
    for width in [32u32, 64] {
        let reg = |n| r(width, n);
        for cc in 0i64..14 {
            let test = || vec![mi(M::CmpRR, vec![reg(0), reg(1)])];
            corpus.push(
                "BCond",
                format!("BCond/w{width}/cc{cc}"),
                diamond(test(), mi(M::BCond, vec![imm(cc), blk(2)])),
                vec![(
                    format!("cc{}", cc ^ 1),
                    diamond(test(), mi(M::BCond, vec![imm(cc ^ 1), blk(2)])),
                )],
            );
        }
        for (row, opcode, other) in [("Cbz", M::Cbz, M::Cbnz), ("Cbnz", M::Cbnz, M::Cbz)] {
            let branch = |opcode, register| diamond(vec![], mi(opcode, vec![register, blk(2)]));
            let mut decoys = vec![(format!("{other:?}"), branch(other, reg(0)))];
            if width == 32 {
                decoys.push(("whole X".into(), branch(opcode, x(0))));
            }
            corpus.push(
                row,
                format!("{row}/w{width}"),
                branch(opcode, reg(0)),
                decoys,
            );
        }
        let bits: &[i64] = if width == 64 {
            &[0, 31, 32, 63]
        } else {
            &[0, 31]
        };
        for &bit in bits {
            let near = if bit == 0 { 1 } else { bit - 1 };
            for (row, opcode, other) in [("Tbz", M::Tbz, M::Tbnz), ("Tbnz", M::Tbnz, M::Tbz)] {
                let branch =
                    |opcode, bit| diamond(vec![], mi(opcode, vec![reg(0), imm(bit), blk(2)]));
                corpus.push(
                    row,
                    format!("{row}/w{width}/#{bit}"),
                    branch(opcode, bit),
                    vec![
                        (format!("{other:?}"), branch(other, bit)),
                        (format!("bit {near}"), branch(opcode, near)),
                    ],
                );
            }
        }
    }
    // `B` to the join, against `B` to the following block (the fall-through
    // arm's own successor is then the other arm's block).
    let mut wrong = diamond(
        vec![mi(M::CmpRR, vec![x(0), x(1)])],
        mi(M::BCond, vec![imm(11), blk(2)]),
    );
    wrong[1].0[1] = mi(M::B, vec![blk(2)]);
    wrong[1].1 = vec![2];
    corpus.push(
        "B",
        "B".into(),
        diamond(
            vec![mi(M::CmpRR, vec![x(0), x(1)])],
            mi(M::BCond, vec![imm(11), blk(2)]),
        ),
        vec![("B to block 2".into(), wrong)],
    );
    // Padding: ALIGNNOP is one word and the pseudo NOP none, between a branch
    // and its targets; each decoy counts one of them the other way (the same
    // displacements over the row of the other kind).
    let padded = |align: MachInst, pseudo: MachInst| {
        vec![
            (
                vec![
                    mi(M::CmpRR, vec![x(0), x(1)]),
                    mi(M::BCond, vec![imm(11), blk(2)]),
                ],
                vec![2, 1],
            ),
            (
                vec![
                    mi(M::EorRR, vec![x(0), x(2), x(3)]),
                    align,
                    mi(M::B, vec![blk(3)]),
                ],
                vec![3],
            ),
            (vec![pseudo, mi(M::SubRR, vec![x(0), x(2), x(3)])], vec![3]),
            (vec![ret()], vec![]),
        ]
    };
    let probe = assemble(
        "padding",
        padded(mi(M::AlignNop, vec![]), mi(M::Nop, vec![])),
    );
    let swap = |from: M, to: M| {
        let mut changed = probe.clone();
        for inst in &mut changed.insts {
            if inst.opcode == from {
                *inst = mi(to, vec![]);
            }
        }
        changed
    };
    let index = corpus.0.len();
    for (row, from, to) in [
        ("AlignNop", M::AlignNop, M::Nop),
        ("Nop", M::Nop, M::AlignNop),
    ] {
        let mut function = probe.clone();
        function.name = format!("probe_{}", index + usize::from(row == "Nop"));
        let mut decoy = swap(from, to);
        decoy.name = function.name.clone();
        corpus.0.push(Probe {
            row,
            name: format!("{row}/padded"),
            function,
            decoys: vec![(format!("{from:?} as {to:?}"), decoy)],
        });
    }
    // Straight-line padding between two value rows.
    corpus.line(
        "AlignNop",
        "AlignNop+Nop/straight".into(),
        vec![
            mi(M::AddRR, vec![x(0), x(0), x(1)]),
            mi(M::Nop, vec![]),
            mi(M::AlignNop, vec![]),
            mi(M::EorRR, vec![x(0), x(0), x(2)]),
        ],
        3,
        vec![mi(M::OrrRR, vec![x(0), x(0), x(2)])],
    );
}

/// Every probe, each with a distinct symbol `probe_<index>`.
pub fn probes() -> Vec<Probe> {
    let mut corpus = Corpus(Vec::new());
    value_probes(32, &mut corpus);
    value_probes(64, &mut corpus);
    extension_and_copy_probes(&mut corpus);
    control_probes(&mut corpus);
    corpus.0
}
