// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The memory-leaf checker on the shapes the proof-grade pipeline emits for
//! load/store leaves (O0 to O3, `aarch64-apple-darwin`), and the controls that
//! must withhold the binding: a wrong slot, a wrong source operand, a swapped
//! width, a wrong stored value, a reordering, a wrong return, a foreign stamp
//! and every domain edge.

use super::*;
use trust_cg_ir::function::{Signature, Type as MType};
use trust_cg_ir::provenance::SourceInstId;
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{InstFlags, MachInst, MachOperand as O, SpecialReg};
use trust_cg_lower::function::{BasicBlock, Signature as LSignature};
use trust_cg_lower::instructions::{Instruction, Opcode as L, Value};
use trust_cg_lower::{Function, Type};

pub(crate) fn x(n: u16) -> O {
    O::PReg(PReg::new(n))
}

pub(crate) fn w(n: u16) -> O {
    O::PReg(PReg::new(32 + n))
}

pub(crate) fn imm(value: i64) -> O {
    O::Imm(value)
}

/// A one-block LIR leaf over `params` returning `returns`; each body entry is
/// `(opcode, args, results)` by value number (arguments are `Value(0..n)`).
pub(crate) fn lir(
    params: &[Type],
    returns: &[Type],
    body: Vec<(L, Vec<u32>, Vec<u32>)>,
) -> Function {
    let mut source = Function::new(
        "leaf",
        LSignature {
            params: params.to_vec(),
            returns: returns.to_vec(),
        },
    );
    let block_params = params
        .iter()
        .enumerate()
        .map(|(i, ty)| (Value(i as u32), ty.clone()))
        .collect();
    let instructions = body
        .into_iter()
        .map(|(opcode, args, results)| Instruction {
            opcode,
            args: args.into_iter().map(Value).collect(),
            results: results.into_iter().map(Value).collect(),
        })
        .collect();
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params: block_params,
            instructions,
            ..Default::default()
        },
    );
    source
}

/// The allocated machine leaf: `insts` in one block, each stamped from the
/// LIR instruction its entry names (`None`: synthetic).
pub(crate) fn allocated(source: &Function, insts: Vec<(M, Vec<O>, Option<u32>)>) -> MachFunction {
    let mtype = |ty: &Type| match ty {
        Type::I32 => MType::I32,
        _ => MType::I64,
    };
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(
            source.signature.params.iter().map(mtype).collect(),
            source.signature.returns.iter().map(mtype).collect(),
        ),
    );
    for (opcode, operands, stamp) in insts {
        let id = machine.push_inst(MachInst::new(opcode, operands));
        machine.append_inst(machine.entry, id);
        if let Some(index) = stamp {
            machine.set_inst_lowering_provenance(
                id,
                LoweringProvenance::SourceInst {
                    id: SourceInstId {
                        block: source.entry_block.0,
                        index,
                    },
                    digest: source.blocks[&source.entry_block].instructions[index as usize]
                        .lowering_digest(),
                    trust_ir_inst: None,
                },
            );
        }
    }
    machine
}

/// Replace instruction `index`'s opcode, with that opcode's own flags.
fn set_opcode(machine: &mut MachFunction, index: usize, opcode: M) {
    let inst = &mut machine.insts[index];
    inst.opcode = opcode;
    inst.flags = MachInst::new(opcode, Vec::new()).flags;
}

fn ret() -> (M, Vec<O>, Option<u32>) {
    (M::Ret, vec![x(30)], None)
}

fn load(ty: Type) -> L {
    L::Load { ty, align: None }
}

fn store(ty: Type) -> L {
    L::Store { ty, align: None }
}

/// `*p` (I64), O1-O3: `ldr x1, [x0]; mov x0, x1; ret`.
pub(crate) fn load64() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64],
        &[Type::I64],
        vec![
            (load(Type::I64), vec![0], vec![1]),
            (L::Return, vec![1], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![x(1), x(0), imm(0)], Some(0)),
            (M::MOVXrr, vec![x(0), x(1)], Some(1)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*(*p + 8)`, O3: `ldr x1, [x0]; ldr x0, [x1, #8]; ret`.
pub(crate) fn chase() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64],
        &[Type::I64],
        vec![
            (load(Type::I64), vec![0], vec![1]),
            (
                L::Iconst {
                    ty: Type::I64,
                    imm: 8,
                },
                vec![],
                vec![2],
            ),
            (L::Iadd, vec![1, 2], vec![3]),
            (load(Type::I64), vec![3], vec![4]),
            (L::Return, vec![4], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![x(1), x(0), imm(0)], Some(0)),
            (M::LdrRI, vec![x(0), x(1), imm(8)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*a <-> *b` (I64), O1-O3.
pub(crate) fn swap64() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64, Type::I64],
        &[],
        vec![
            (load(Type::I64), vec![0], vec![2]),
            (load(Type::I64), vec![1], vec![3]),
            (store(Type::I64), vec![3, 0], vec![]),
            (store(Type::I64), vec![2, 1], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![x(2), x(0), imm(0)], Some(0)),
            (M::LdrRI, vec![x(3), x(1), imm(0)], Some(1)),
            (M::StrRI, vec![x(3), x(0), imm(0)], Some(2)),
            (M::StrRI, vec![x(2), x(1), imm(0)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*(p + 16)` (I64), O1: `add x1, x0, #16; ldr x0, [x1]; ret`.
fn load64_off_o1() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64],
        &[Type::I64],
        vec![
            (
                L::Iconst {
                    ty: Type::I64,
                    imm: 16,
                },
                vec![],
                vec![1],
            ),
            (L::Iadd, vec![0, 1], vec![2]),
            (load(Type::I64), vec![2], vec![3]),
            (L::Return, vec![3], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::AddRI, vec![x(1), x(0), imm(16)], Some(1)),
            (M::LdrRI, vec![x(0), x(1), imm(0)], Some(2)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*(p + 16)` (I64), O0: a dead MOVZ, the ADD and the load, NOP copies.
fn load64_off_o0() -> (Function, MachFunction) {
    let (source, _) = load64_off_o1();
    let machine = allocated(
        &source,
        vec![
            (M::Nop, vec![x(0), x(0)], None),
            (M::Movz, vec![x(1), imm(16)], Some(0)),
            (M::AddRI, vec![x(1), x(0), imm(16)], Some(1)),
            (M::LdrRI, vec![x(0), x(1), imm(0)], Some(2)),
            (M::Nop, vec![x(0), x(0)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `source` with every `Iadd` respelled as the byte-stride `ArrayGep { elem_ty:
/// I8 }` the adapter emits for a byte offset since `b79533c9c`.
fn byte_stride(mut source: Function) -> Function {
    let block = source.blocks.get_mut(&source.entry_block).unwrap();
    for inst in &mut block.instructions {
        if matches!(inst.opcode, L::Iadd) {
            inst.opcode = L::ArrayGep { elem_ty: Type::I8 };
        }
    }
    source
}

/// [`chase`] as the pipeline now lowers it: `*(*p + 8)` through a byte-stride
/// address, O3: `ldr x1, [x0]; ldr x0, [x1, #8]; ret`.
fn chase_byte_stride() -> (Function, MachFunction) {
    let source = byte_stride(chase().0);
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![x(1), x(0), imm(0)], Some(0)),
            (M::LdrRI, vec![x(0), x(1), imm(8)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*(p + 16)` (I64) through a byte-stride address, O0: the dead MOVZ, the
/// ADD and the load, NOP copies (the body the pipeline emits on Linux
/// AArch64 at `8faee6c6f`).
fn load64_off_byte_stride_o0() -> (Function, MachFunction) {
    let source = byte_stride(load64_off_o1().0);
    let machine = allocated(
        &source,
        vec![
            (M::Nop, vec![x(0), x(0)], None),
            (M::Movz, vec![x(1), imm(16)], Some(0)),
            (M::AddRI, vec![x(1), x(0), imm(16)], Some(1)),
            (M::LdrRI, vec![x(0), x(1), imm(0)], Some(2)),
            (M::Nop, vec![x(0), x(0)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*p as u8` returned as I32, O0: `ldrb w1, [x0]; uxtb w0, w1; ret`.
fn load8_o0() -> (Function, MachFunction) {
    let mut source = lir(
        &[Type::I64],
        &[Type::I32],
        vec![
            (load(Type::I8), vec![0], vec![1]),
            (
                L::Uextend {
                    from_ty: Type::I8,
                    to_ty: Type::I32,
                },
                vec![1],
                vec![2],
            ),
            (L::Return, vec![2], vec![]),
        ],
    );
    source.value_types.insert(Value(2), Type::I32);
    let machine = allocated(
        &source,
        vec![
            (M::Nop, vec![x(0), x(0)], None),
            (M::LdrbRI, vec![w(1), x(0), imm(0)], Some(0)),
            (M::Uxtb, vec![w(0), w(1)], Some(1)),
            (M::Nop, vec![w(0), w(0)], Some(2)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*p as u16` returned as I32, O3: `ldrh w1, [x0]; mov w0, w1; ret`.
fn load16_o3() -> (Function, MachFunction) {
    let mut source = lir(
        &[Type::I64],
        &[Type::I32],
        vec![
            (load(Type::I16), vec![0], vec![1]),
            (
                L::Uextend {
                    from_ty: Type::I16,
                    to_ty: Type::I32,
                },
                vec![1],
                vec![2],
            ),
            (L::Return, vec![2], vec![]),
        ],
    );
    source.value_types.insert(Value(2), Type::I32);
    let machine = allocated(
        &source,
        vec![
            (M::LdrhRI, vec![w(1), x(0), imm(0)], Some(0)),
            (M::MOVWrr, vec![w(0), w(1)], Some(1)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*(p + 8) as u32`, O3: `ldr w1, [x0, #8]; mov w0, w1; ret`.
fn load32_gep_o3() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64],
        &[Type::I32],
        vec![
            (
                L::Iconst {
                    ty: Type::I64,
                    imm: 8,
                },
                vec![],
                vec![1],
            ),
            (L::Iadd, vec![0, 1], vec![2]),
            (load(Type::I32), vec![2], vec![3]),
            (L::Return, vec![3], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![w(1), x(0), imm(8)], Some(2)),
            (M::MOVWrr, vec![w(0), w(1)], Some(3)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*p = v as u8`, O0: the synthetic `mov w1, w1` formal copy, then `strb`.
fn store8_o0() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64, Type::I8],
        &[],
        vec![
            (store(Type::I8), vec![1, 0], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::Nop, vec![x(0), x(0)], None),
            (M::MOVWrr, vec![w(1), x(1)], None),
            (M::StrbRI, vec![w(1), x(0), imm(0)], Some(0)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*p = v` (U32), O1-O3: `str w1, [x0]; ret`.
fn store32() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64, Type::I32],
        &[],
        vec![
            (store(Type::I32), vec![1, 0], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![(M::StrRI, vec![w(1), x(0), imm(0)], Some(0)), ret()],
    );
    (source, machine)
}

/// `*p = 42`, O1-O3: `movz x1, #42; str x1, [x0]; ret`.
fn store_const() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64],
        &[],
        vec![
            (
                L::Iconst {
                    ty: Type::I64,
                    imm: 42,
                },
                vec![],
                vec![1],
            ),
            (store(Type::I64), vec![1, 0], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::Movz, vec![x(1), imm(42)], Some(0)),
            (M::StrRI, vec![x(1), x(0), imm(0)], Some(1)),
            ret(),
        ],
    );
    (source, machine)
}

/// `*dst = *src` (I64): `ldr x2, [x1]; str x2, [x0]; ret`.
pub(crate) fn copy64() -> (Function, MachFunction) {
    let source = lir(
        &[Type::I64, Type::I64],
        &[],
        vec![
            (load(Type::I64), vec![1], vec![2]),
            (store(Type::I64), vec![2, 0], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![
            (M::LdrRI, vec![x(2), x(1), imm(0)], Some(0)),
            (M::StrRI, vec![x(2), x(0), imm(0)], Some(1)),
            ret(),
        ],
    );
    (source, machine)
}

#[test]
fn binds_every_access_of_the_pipeline_shapes() {
    type Fixture = fn() -> (Function, MachFunction);
    /// `(load, bytes, offset, base, data)` of each expected contract access.
    type Expected = &'static [(bool, u32, i64, u8, u8)];
    let cases: [(&str, Fixture, Expected); 15] = [
        ("load64", load64, &[(true, 8, 0, 0, 1)]),
        ("chase", chase, &[(true, 8, 0, 0, 1), (true, 8, 8, 1, 0)]),
        (
            "chase_byte_stride",
            chase_byte_stride,
            &[(true, 8, 0, 0, 1), (true, 8, 8, 1, 0)],
        ),
        (
            "load64_off_byte_stride_o0",
            load64_off_byte_stride_o0,
            &[(true, 8, 0, 1, 0)],
        ),
        (
            "swap64",
            swap64,
            &[
                (true, 8, 0, 0, 2),
                (true, 8, 0, 1, 3),
                (false, 8, 0, 0, 3),
                (false, 8, 0, 1, 2),
            ],
        ),
        ("load64_off_o1", load64_off_o1, &[(true, 8, 0, 1, 0)]),
        ("load64_off_o0", load64_off_o0, &[(true, 8, 0, 1, 0)]),
        ("load8_o0", load8_o0, &[(true, 1, 0, 0, 1)]),
        ("load16_o3", load16_o3, &[(true, 2, 0, 0, 1)]),
        ("load32_gep_o3", load32_gep_o3, &[(true, 4, 8, 0, 1)]),
        ("store8_o0", store8_o0, &[(false, 1, 0, 0, 1)]),
        ("store32", store32, &[(false, 4, 0, 0, 1)]),
        ("store_const", store_const, &[(false, 8, 0, 0, 1)]),
        ("copy64", copy64, &[(true, 8, 0, 1, 2), (false, 8, 0, 0, 2)]),
        (
            "load64_twice",
            || {
                let (source, mut machine) = load64();
                // A second, inert NOP tombstone outside the block changes nothing.
                machine.push_inst(MachInst::new(M::Nop, vec![x(3), x(3)]));
                (source, machine)
            },
            &[(true, 8, 0, 0, 1)],
        ),
    ];
    for (name, fixture, expected) in cases {
        let (source, machine) = fixture();
        let leaf = source_bound_memory_leaf(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
        assert_eq!(leaf.accesses().len(), expected.len(), "{name}");
        for (position, (access, (load, bytes, offset, base, data))) in leaf
            .accesses()
            .iter()
            .zip(expected.iter().copied())
            .enumerate()
        {
            assert_eq!(access.position, position, "{name}");
            assert_eq!(
                access.contract,
                ContractAccess::scalar(load, bytes, offset, base, data, false),
                "{name} access {position}"
            );
            let inst = &machine.insts[access.instruction.0 as usize];
            assert!(
                access.contract.check(&memory_access(inst).unwrap()).is_ok(),
                "{name} access {position}"
            );
        }
    }
}

fn refusal(source: &Function, machine: &MachFunction) -> MemoryLeafRefusal {
    source_bound_memory_leaf(source, machine).expect_err("the binding must be withheld")
}

fn trace_refusal(source: &Function, machine: &MachFunction) -> (usize, String) {
    match refusal(source, machine) {
        MemoryLeafRefusal::Trace { position, what } => (position, what),
        other => panic!("expected a trace disagreement, got {other}"),
    }
}

/// A load at the wrong slot, through the wrong source operand, with a
/// swapped width, a store of the wrong value or to the wrong slot: each is a
/// named trace disagreement at the access it corrupts.
#[test]
fn corrupted_accesses_withhold_the_binding_by_name() {
    // Wrong slot: the chase's second load reads +16 where the source reads +8.
    let (source, mut machine) = chase();
    machine.insts[1].operands[2] = imm(16);
    assert_eq!(
        trace_refusal(&source, &machine),
        (1, "the offset does not reach the source's address".into())
    );
    // Wrong source operand: swap64's first load reads through x1 (`b`) where
    // the source loads from `a` (x0).
    let (source, mut machine) = swap64();
    machine.insts[0].operands[1] = x(1);
    assert_eq!(
        trace_refusal(&source, &machine),
        (
            0,
            "the base register does not hold the source pointer plus a constant".into()
        )
    );
    // Swapped width: a 4-byte LDR W for the source's 8-byte load.
    let (source, mut machine) = load64();
    machine.insts[0].operands[0] = w(1);
    assert_eq!(
        trace_refusal(&source, &machine),
        (0, "another access width than the source's".into())
    );
    // Swapped width the other way: LDRB for a 2-byte source load.
    let (source, mut machine) = load16_o3();
    set_opcode(&mut machine, 0, M::LdrbRI);
    assert_eq!(
        trace_refusal(&source, &machine),
        (0, "another access width than the source's".into())
    );
    // A store of the wrong register: swap64's first store writes x2 (`*a`)
    // back to `a`.
    let (source, mut machine) = swap64();
    machine.insts[2].operands[0] = x(2);
    assert_eq!(
        trace_refusal(&source, &machine),
        (
            2,
            "the stored register does not hold the source's value".into()
        )
    );
    // A store of the wrong constant.
    let (source, mut machine) = store_const();
    machine.insts[0].operands[1] = imm(43);
    assert_eq!(
        trace_refusal(&source, &machine),
        (
            0,
            "the stored register does not hold the source's value".into()
        )
    );
    // A store where the source loads.
    let (source, mut machine) = load64();
    set_opcode(&mut machine, 0, M::StrRI);
    assert_eq!(
        trace_refusal(&source, &machine),
        (0, "a load where the source stores, or the reverse".into())
    );
    // An ADD that moves the base: the O1 load64_off adds 8, not 16.
    let (source, mut machine) = load64_off_o1();
    machine.insts[0].operands[2] = imm(8);
    assert_eq!(
        trace_refusal(&source, &machine),
        (0, "the offset does not reach the source's address".into())
    );
}

/// A byte-stride address is its 64-bit sum and nothing else: an access past
/// it, an ADD of the wrong offset, a wider element (a product this linear
/// domain does not model) and a narrow index each bind nothing, by name.
#[test]
fn a_byte_stride_address_binds_only_as_its_sum() {
    // Wrong slot: the second load reads +16 where the source's address is +8.
    let (source, mut machine) = chase_byte_stride();
    machine.insts[1].operands[2] = imm(16);
    assert_eq!(
        trace_refusal(&source, &machine),
        (1, "the offset does not reach the source's address".into())
    );
    // Wrong offset materialized at O0: `add x1, x0, #24` for `p + 16`.
    let (source, mut machine) = load64_off_byte_stride_o0();
    machine.insts[2].operands[2] = imm(24);
    assert_eq!(
        trace_refusal(&source, &machine),
        (0, "the offset does not reach the source's address".into())
    );
    // A two-byte element strides `index * 2`: outside the domain, by name.
    let (mut source, machine) = chase_byte_stride();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[2]
        .opcode = L::ArrayGep { elem_ty: Type::I16 };
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Source("instruction 2: ArrayGep".into())
    );
    // A 32-bit index is no LIR `ArrayGep` index: refused, never read as its
    // low bits.
    let (mut source, machine) = load64_off_byte_stride_o0();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = L::Iconst {
        ty: Type::I32,
        imm: 16,
    };
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Source("a byte-stride address narrower than 64 bits".into())
    );
}

/// The lock-step trace refuses a legal-looking reordering too: it cannot
/// tell one from a miscompile, so it binds nothing (never a rejection).
#[test]
fn reordered_missing_or_extra_accesses_bind_nothing() {
    let (source, mut machine) = swap64();
    machine.blocks[0].insts.swap(0, 1);
    assert!(matches!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Trace { position: 0, .. } | MemoryLeafRefusal::Stamp { .. }
    ));
    let (source, full) = swap64();
    let machine = allocated(
        &source,
        full.blocks[0]
            .insts
            .iter()
            .filter(|id| id.0 != 3)
            .map(|id| {
                let inst = &full.insts[id.0 as usize];
                let stamp = full
                    .inst_lowering_provenance(*id)
                    .source_id()
                    .map(|stamp| stamp.index);
                (inst.opcode, inst.operands.clone(), stamp)
            })
            .collect(),
    );
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::TraceLength {
            machine: 3,
            expected: 4
        }
    );
    let (source, mut machine) = load64();
    let extra = machine.push_inst(MachInst::new(M::LdrRI, vec![x(2), x(0), imm(0)]));
    machine.blocks[0].insts.insert(1, extra);
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::TraceLength {
            machine: 2,
            expected: 1
        }
    );
}

#[test]
fn a_wrong_return_or_a_foreign_stamp_binds_nothing() {
    // The chase's second load lands in x2, so x0 still holds the pointer.
    let (source, mut machine) = chase();
    machine.insts[1].operands[0] = x(2);
    assert_eq!(refusal(&source, &machine), MemoryLeafRefusal::Return);
    // load8 returned through W0 without the zero extension of its byte is
    // still the byte: LDRB already zero-extends, so `mov w0, w1` binds too.
    let (source, mut machine) = load8_o0();
    set_opcode(&mut machine, 2, M::MOVWrr);
    assert!(source_bound_memory_leaf(&source, &machine).is_ok());
    // The swap's second load is stamped from the first load's LIR row.
    let (source, mut machine) = swap64();
    let stamp = machine.inst_lowering_provenance(InstId(0));
    machine.set_inst_lowering_provenance(InstId(1), stamp);
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Stamp {
            position: 1,
            stamped: "lir0.0".into(),
            block: 0,
            index: 1
        }
    );
}

/// A register narrowed by a 32-bit copy never stands for a wider source
/// value: `mov w1, w1; str x1, [x0]` stores zext32(v), not the source's
/// 64-bit `v`, and `ldr x1, [x0]; mov w0, w1; ret` returns the low half of
/// `*p`, not the source's 64-bit `*p`. Each control first binds unnarrowed.
#[test]
fn a_narrowed_register_never_feeds_a_wider_store_or_return() {
    let source = lir(
        &[Type::I64, Type::I64],
        &[],
        vec![
            (store(Type::I64), vec![1, 0], vec![]),
            (L::Return, vec![], vec![]),
        ],
    );
    let store64 = |narrow: bool| {
        let mut body = Vec::new();
        if narrow {
            body.push((M::MOVWrr, vec![w(1), w(1)], None));
        }
        body.push((M::StrRI, vec![x(1), x(0), imm(0)], Some(0)));
        body.push(ret());
        allocated(&source, body)
    };
    assert!(source_bound_memory_leaf(&source, &store64(false)).is_ok());
    assert_eq!(
        trace_refusal(&source, &store64(true)),
        (
            0,
            "the stored register does not hold the source's value".into()
        )
    );
    let (source, machine) = load64();
    assert!(source_bound_memory_leaf(&source, &machine).is_ok());
    let mut narrowed = machine;
    set_opcode(&mut narrowed, 1, M::MOVWrr);
    narrowed.insts[1].operands = vec![w(0), w(1)];
    assert_eq!(refusal(&source, &narrowed), MemoryLeafRefusal::Return);
}

#[test]
fn shapes_outside_the_domain_are_named_and_bind_nothing() {
    let machine_refusal = |source: &Function, machine: &MachFunction| {
        matches!(refusal(source, machine), MemoryLeafRefusal::Machine(_))
    };
    // An SP-based access (a spill or frame slot).
    let (source, mut machine) = load64();
    machine.insts[0].operands[1] = O::Special(SpecialReg::SP);
    assert!(machine_refusal(&source, &machine));
    // A write to a callee-saved register.
    let (source, mut machine) = load64();
    machine.insts[0].operands[0] = x(19);
    assert!(machine_refusal(&source, &machine));
    // A call.
    let (source, mut machine) = load64();
    let call = machine.push_inst(MachInst::new(M::Bl, vec![O::Symbol("callee".into())]));
    machine.blocks[0].insts.insert(1, call);
    assert!(machine_refusal(&source, &machine));
    // Hidden effects on an access.
    let (source, mut machine) = load64();
    machine.insts[0].flags = InstFlags::HAS_SIDE_EFFECTS;
    assert!(machine_refusal(&source, &machine));
    // A sign-extending load is no access the decomposition admits.
    let (source, mut machine) = load16_o3();
    set_opcode(&mut machine, 0, M::LdrshRI);
    assert!(machine_refusal(&source, &machine));
    // A 32-bit ADD of the pointer.
    let (source, mut machine) = load64_off_o1();
    machine.insts[0].operands[0] = w(1);
    assert!(machine_refusal(&source, &machine));
    // A source without memory, a volatile access, a narrow return.
    let pure = lir(
        &[Type::I64],
        &[Type::I64],
        vec![(L::Return, vec![0], vec![])],
    );
    let pure_machine = allocated(&pure, vec![(M::MOVXrr, vec![x(0), x(0)], None), ret()]);
    assert!(matches!(
        refusal(&pure, &pure_machine),
        MemoryLeafRefusal::Source(_)
    ));
    let (mut source, machine) = load64();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = L::VolatileLoad {
        ty: Type::I64,
        align: None,
    };
    assert!(matches!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Source(_)
    ));
    let narrow = lir(
        &[Type::I64],
        &[Type::I8],
        vec![
            (load(Type::I8), vec![0], vec![1]),
            (L::Return, vec![1], vec![]),
        ],
    );
    let narrow_machine = allocated(
        &narrow,
        vec![(M::LdrbRI, vec![w(0), x(0), imm(0)], Some(0)), ret()],
    );
    assert!(matches!(
        refusal(&narrow, &narrow_machine),
        MemoryLeafRefusal::Source(_)
    ));
    // Another function's source.
    let (mut source, machine) = load64();
    source.name.push_str("_other");
    assert!(machine_refusal(&source, &machine));
}

/// Pad a real load/add leaf with dead, admitted constants before its return.
/// Its actual access and the machine stamp stay unchanged.
fn source_instruction_boundary(instructions: usize) -> (Function, MachFunction) {
    let (mut source, machine) = load64_off_o1();
    let block = source.blocks.get_mut(&source.entry_block).unwrap();
    let returned = block.instructions.pop().unwrap();
    while block.instructions.len() + 1 < instructions {
        block.instructions.push(Instruction {
            opcode: L::Iconst {
                ty: Type::I64,
                imm: 0,
            },
            args: Vec::new(),
            results: vec![Value(block.instructions.len() as u32 + 1)],
        });
    }
    block.instructions.push(returned);
    assert_eq!(block.instructions.len(), instructions);
    (source, machine)
}

fn source_reason(source: &Function, machine: &MachFunction) -> String {
    match refusal(source, machine) {
        MemoryLeafRefusal::Source(reason) => reason,
        other => panic!("expected an optional source binding refusal, got {other}"),
    }
}

#[test]
fn source_cardinality_exact_instruction_bound_binds_load_add() {
    assert_eq!(MAX_SOURCE_INSTRUCTIONS, 256);
    let (source, machine) = source_instruction_boundary(MAX_SOURCE_INSTRUCTIONS);
    let before = format!("{source:?}");
    let leaf = source_bound_memory_leaf(&source, &machine).unwrap();
    assert!(std::ptr::eq(leaf.source(), &source));
    assert!(std::ptr::eq(leaf.machine(), &machine));
    assert_eq!(leaf.accesses().len(), 1);
    assert_eq!(leaf.accesses()[0].source_index, 2);
    assert_eq!(
        leaf.accesses()[0].contract,
        ContractAccess::scalar(true, 8, 0, 1, 0, false)
    );
    assert_eq!(format!("{source:?}"), before);

    let (source, mut machine) = source_instruction_boundary(MAX_SOURCE_INSTRUCTIONS + 1);
    let before = format!("{source:?}");
    // The source bound is checked before constructing any machine chain.
    machine.blocks.clear();
    assert_eq!(
        source_reason(&source, &machine),
        "more than 256 source instructions"
    );
    assert_eq!(format!("{source:?}"), before);
}

#[test]
fn source_cardinality_hints_fit_exactly_the_inferred_value_inventory() {
    let (mut source, machine) = source_instruction_boundary(MAX_SOURCE_INSTRUCTIONS);
    source.value_types.insert(Value(0), Type::I64);
    let results: Vec<Value> = source.blocks[&source.entry_block]
        .instructions
        .iter()
        .flat_map(|inst| inst.results.iter().copied())
        .collect();
    for value in results {
        source.value_types.insert(value, Type::I64);
    }
    assert_eq!(source.value_types.len(), MAX_SOURCE_INSTRUCTIONS);
    assert!(source_bound_memory_leaf(&source, &machine).is_ok());
    source
        .value_types
        .insert(Value(MAX_SOURCE_INSTRUCTIONS as u32), Type::I64);
    assert_eq!(
        source_reason(&source, &machine),
        "more type hints than arguments and instruction results"
    );

    // A bounded number of hints still reaches the original detailed check.
    let (mut source, machine) = load64();
    source.value_types.insert(Value(99), Type::I64);
    assert_eq!(
        source_reason(&source, &machine),
        "a type hint disagrees with the inferred width"
    );
}

#[test]
fn source_cardinality_entry_parameters_use_the_existing_eight_argument_bound() {
    assert_eq!(MAX_SOURCE_ARGUMENTS, 8);
    let parameters: [Type; MAX_SOURCE_ARGUMENTS] = std::array::from_fn(|_| Type::I64);
    let source = lir(
        &parameters,
        &[Type::I64],
        vec![
            (load(Type::I64), vec![0], vec![8]),
            (L::Return, vec![8], vec![]),
        ],
    );
    let machine = allocated(
        &source,
        vec![(M::LdrRI, vec![x(0), x(0), imm(0)], Some(0)), ret()],
    );
    assert!(source_bound_memory_leaf(&source, &machine).is_ok());
    let mut oversized = source.clone();
    oversized
        .blocks
        .get_mut(&oversized.entry_block)
        .unwrap()
        .params
        .push((Value(99), Type::I64));
    assert_eq!(
        source_reason(&oversized, &machine),
        "more than eight entry parameters"
    );

    // Within the existing cardinality, keep the old identity/type refusal.
    let mut malformed = source;
    malformed
        .blocks
        .get_mut(&malformed.entry_block)
        .unwrap()
        .params[0]
        .0 = Value(99);
    assert_eq!(
        source_reason(&malformed, &machine),
        "entry parameters disagree with the Value(0..n) signature convention"
    );
}

#[test]
fn source_cardinality_large_operand_and_result_vectors_bind_nothing() {
    for length in [3, 65_536] {
        let (mut source, machine) = load64_off_o1();
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[1]
            .args = vec![Value(0); length];
        assert_eq!(
            source_reason(&source, &machine),
            "an instruction exceeds two operands"
        );
    }
    for length in [2, 65_536] {
        let (mut source, machine) = load64_off_o1();
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[1]
            .results = vec![Value(2); length];
        assert_eq!(
            source_reason(&source, &machine),
            "an instruction exceeds one result"
        );
    }
    // Two operands and one result are the actual admitted add shape.
    let (source, machine) = load64_off_o1();
    assert!(source_bound_memory_leaf(&source, &machine).is_ok());
}

#[test]
fn source_cardinality_preserves_bounded_malformed_refusal_order() {
    let (mut source, machine) = load64_off_o1();
    source.signature.params[0] = Type::F64;
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[1]
        .args
        .pop();
    assert_eq!(source_reason(&source, &machine), "a non-integer argument");

    let (mut source, machine) = load64_off_o1();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[1]
        .args
        .pop();
    assert_eq!(
        source_reason(&source, &machine),
        "wrong operand or result arity"
    );

    let (mut source, machine) = load64_off_o1();
    let block = source.blocks.get_mut(&source.entry_block).unwrap();
    block.instructions[1].args[0] = Value(99);
    block.instructions[2].opcode = L::Trap;
    source.value_types.insert(Value(99), Type::F64);
    assert_eq!(
        source_reason(&source, &machine),
        "a use of an undefined value"
    );

    let (mut source, machine) = load64();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions
        .push(Instruction {
            opcode: L::Trap,
            args: Vec::new(),
            results: Vec::new(),
        });
    assert_eq!(
        source_reason(&source, &machine),
        "an instruction follows the return"
    );
}

#[test]
fn source_cardinality_preserves_earlier_source_and_name_refusals() {
    let (mut source, machine) = source_instruction_boundary(MAX_SOURCE_INSTRUCTIONS + 1);
    source.stack_protector = StackProtectorMode::StackGuard;
    assert_eq!(
        source_reason(&source, &machine),
        "requires one block without stack, EH or aggregate ABI metadata"
    );
    source.stack_protector = StackProtectorMode::None;
    source.signature.params = vec![Type::I64; MAX_SOURCE_ARGUMENTS + 1];
    assert_eq!(
        source_reason(&source, &machine),
        "requires at most eight arguments and one return"
    );
    source.name.push_str("_foreign");
    assert_eq!(
        refusal(&source, &machine),
        MemoryLeafRefusal::Machine("source and machine name different functions".into())
    );
}

#[test]
fn source_cardinality_ignores_metadata_the_leaf_does_not_traverse() {
    let (mut source, machine) = load64_off_o1();
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .source_locs = vec![None; 65_536];
    source
        .trust_ir_origins
        .insert(source.entry_block, vec![None; 65_536]);
    for index in 0..=MAX_SOURCE_INSTRUCTIONS {
        source.pure_callees.insert(format!("unused_{index}"));
    }
    let leaf = source_bound_memory_leaf(&source, &machine).unwrap();
    assert_eq!(leaf.accesses().len(), 1);
    assert!(std::ptr::eq(leaf.source(), &source));
}

#[test]
fn source_cardinality_unsupported_opcode_diagnostics_do_not_print_payloads() {
    use trust_cg_lower::instructions::{Block, DirectCallBinding};

    for opcode in [
        L::Call {
            name: "untrusted_payload".repeat(65_536),
            binding: DirectCallBinding::Interposable,
        },
        L::Switch {
            cases: vec![(0, Block(99)); 65_536],
            default: Block(0),
        },
    ] {
        let expected = match &opcode {
            L::Call { .. } => "instruction 0: Call",
            L::Switch { .. } => "instruction 0: Switch",
            _ => unreachable!(),
        };
        let (mut source, machine) = load64();
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = opcode;
        assert_eq!(source_reason(&source, &machine), expected);
    }
}
