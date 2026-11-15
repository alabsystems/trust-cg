//! Full-pipeline operand-shape lock for scalar FP-to-integer conversions.
//!
//! Regression for the `FcvtzsRR`/`FcvtzuRR` selector/encoder contract split:
//! instruction selection used to append a third pseudo-operand
//! (`Imm(source_fp_width)`) as a post-selection width hint, while the final
//! encoder's `encode_scalar_fp_int_conversion` accepts exactly two register
//! operands. Every FP-to-int cast then failed encoding with
//! `invalid operand at index 2 for FcvtzsRR: scalar integer/FP conversion
//! requires exactly two register operands`, which took nine end-to-end and
//! differential suites red on every host.
//!
//! The encoder is the side that matches the architecture. FCVTZS/FCVTZU
//! (scalar, integer) in the Arm ARM (C7.2, "Conversion between floating-point
//! and integer" class, `sf 0 0 11110 ftype 1 11 00x 000000 Rn Rd`) name two
//! registers only: `Rd` is the W/X general-purpose destination selected by
//! `sf`, `Rn` is the H/S/D source selected by `ftype`. Index 2 does not exist
//! in the instruction; the selector must not invent it, and the encoder must
//! keep refusing it rather than silently dropping a trailing operand.
//!
//! Unlike the native link-and-run suites, this test needs no C compiler and no
//! particular host: it runs selection, allocation and encoding through the
//! public `Compiler` for both AArch64 object formats and reads the emitted
//! `.text`/`__text` words back, so it fails on the old selector on any host.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_function};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_ir::function::{MachFunction, Signature, Type as MachType};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{D0, S0, W0, X0};
use trust_ir::{
    Block, BlockId, CastOp, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Object-file text extraction (Mach-O 64 and ELF64, both little-endian).
// ---------------------------------------------------------------------------

fn le_u32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn le_u64(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

/// `__text` of a 64-bit little-endian Mach-O object (`LC_SEGMENT_64` = 0x19).
fn macho_text(bytes: &[u8]) -> Option<&[u8]> {
    const MACH_HEADER_64: usize = 32;
    const SEGMENT_COMMAND_64: usize = 72;
    const SECTION_64: usize = 80;
    let sizeofcmds = le_u32(bytes, 20) as usize;
    let mut offset = MACH_HEADER_64;
    while offset + 8 <= MACH_HEADER_64 + sizeofcmds {
        let cmd = le_u32(bytes, offset);
        let cmdsize = le_u32(bytes, offset + 4) as usize;
        if cmd == 0x19 {
            let nsects = le_u32(bytes, offset + 64) as usize;
            let mut section = offset + SEGMENT_COMMAND_64;
            for _ in 0..nsects {
                let name = &bytes[section..section + 16];
                let name = &name[..name.iter().position(|&b| b == 0).unwrap_or(16)];
                if name == b"__text" {
                    let size = le_u64(bytes, section + 40) as usize;
                    let file_offset = le_u32(bytes, section + 48) as usize;
                    return bytes.get(file_offset..file_offset + size);
                }
                section += SECTION_64;
            }
        }
        offset += cmdsize;
    }
    None
}

/// `.text` of an ELF64 little-endian relocatable object.
fn elf_text(bytes: &[u8]) -> Option<&[u8]> {
    let shoff = le_u64(bytes, 0x28) as usize;
    let shentsize = usize::from(u16::from_le_bytes([bytes[0x3a], bytes[0x3b]]));
    let shnum = usize::from(u16::from_le_bytes([bytes[0x3c], bytes[0x3d]]));
    let shstrndx = usize::from(u16::from_le_bytes([bytes[0x3e], bytes[0x3f]]));
    let header = |index: usize| shoff + index * shentsize;
    let strtab_offset = le_u64(bytes, header(shstrndx) + 0x18) as usize;
    for index in 0..shnum {
        let at = header(index);
        let name_offset = strtab_offset + le_u32(bytes, at) as usize;
        let name = &bytes[name_offset..];
        let name = &name[..name.iter().position(|&b| b == 0).unwrap_or(0)];
        if name == b".text" {
            let file_offset = le_u64(bytes, at + 0x18) as usize;
            let size = le_u64(bytes, at + 0x20) as usize;
            return bytes.get(file_offset..file_offset + size);
        }
    }
    None
}

fn text_words(object: &[u8]) -> Vec<u32> {
    let text = match object.get(..4) {
        Some(b"\x7fELF") => elf_text(object),
        Some(magic) if le_u32(magic, 0) == 0xfeed_facf => macho_text(object),
        other => panic!("unrecognised object magic {other:?}"),
    }
    .expect("object must carry a text section");
    assert_eq!(text.len() % 4, 0, "AArch64 text must be whole instructions");
    text.as_chunks::<4>()
        .0
        .iter()
        .map(|word| le_u32(word, 0))
        .collect()
}

// ---------------------------------------------------------------------------
// FCVTZS/FCVTZU (scalar, integer) word shape.
// ---------------------------------------------------------------------------

/// Fixed bits of the FCVTZ{S,U} scalar-integer class with `sf`, `ftype`, the
/// U opcode bit and the two register fields masked out.
const FCVTZ_FAMILY_MASK: u32 = 0x7f3e_fc00;
const FCVTZ_FAMILY_BITS: u32 = 0x1e38_0000;
const REGISTER_FIELDS: u32 = 0x3ff;

fn expected_fcvtz(sf_64: bool, ftype: u32, unsigned: bool) -> u32 {
    (u32::from(sf_64) << 31) | FCVTZ_FAMILY_BITS | (ftype << 22) | (u32::from(unsigned) << 16)
}

struct Shape {
    source: Ty,
    destination: Ty,
    op: CastOp,
}

fn shapes() -> Vec<Shape> {
    let mut shapes = Vec::new();
    for source in [Ty::F32, Ty::F64] {
        for destination in [Ty::I8, Ty::I16, Ty::I32, Ty::I64] {
            shapes.push(Shape {
                source: source.clone(),
                destination,
                op: CastOp::FPToSI,
            });
        }
        for destination in [Ty::U8, Ty::U16, Ty::U32, Ty::U64] {
            shapes.push(Shape {
                source: source.clone(),
                destination,
                op: CastOp::FPToUI,
            });
        }
    }
    shapes
}

fn module_for(shape: &Shape) -> Module {
    let mut module = Module::new("fp_to_int_shape");
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![shape.source.clone()],
            returns: vec![shape.destination.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "cast", func_ty, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), shape.source.clone())],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: shape.op,
                src_ty: shape.source.clone(),
                dst_ty: shape.destination.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn expected_word(shape: &Shape) -> u32 {
    let ftype = match shape.source {
        Ty::F32 => 0b00,
        Ty::F64 => 0b01,
        ref other => panic!("unexpected source {other:?}"),
    };
    // I8/I16/U8/U16 are carried in a W register: the architectural FCVTZ has
    // no narrower form, and the selector's Gpr32 class must reach the encoder
    // as sf = 0, not as a hard-coded X width.
    let sf_64 = matches!(shape.destination, Ty::I64 | Ty::U64);
    expected_fcvtz(sf_64, ftype, matches!(shape.op, CastOp::FPToUI))
}

#[test]
fn selected_fp_to_int_casts_encode_one_two_register_fcvtz_per_shape() {
    let mut checked = 0usize;
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        let spec = TargetSpec::parse(triple).unwrap();
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for shape in shapes() {
                let label = format!(
                    "{triple} {opt_level:?} {:?} {:?} -> {:?}",
                    shape.op, shape.source, shape.destination
                );
                let compiler = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        ..CompilerConfig::default()
                    },
                    spec,
                )
                .with_codegen_license(permit_unlicensed());
                let result = compiler
                    .compile(&module_for(&shape))
                    .unwrap_or_else(|error| panic!("{label}: {error:?}"));
                let words = text_words(&result.object_code);
                let fcvtz: Vec<u32> = words
                    .iter()
                    .copied()
                    .filter(|word| word & FCVTZ_FAMILY_MASK == FCVTZ_FAMILY_BITS)
                    .collect();
                assert_eq!(
                    fcvtz.len(),
                    1,
                    "{label}: exactly one scalar FCVTZ expected in {words:08x?}"
                );
                let word = fcvtz[0];
                assert_eq!(
                    word & !REGISTER_FIELDS,
                    expected_word(&shape),
                    "{label}: FCVTZ word {word:08x} has wrong sf/ftype/U fields"
                );
                // Rn is the FP source and Rd the GPR destination; both are
                // plain 5-bit register numbers with no third operand encoded
                // anywhere (bits 15:10 of the class are fixed zero).
                assert_eq!(word & 0xfc00, 0, "{label}: bits 15:10 must be zero");
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 2 * 2 * 16);
}

/// The historical three-operand shape must still be refused at the function
/// encoder, naming index 2, rather than silently encoded as if the trailing
/// hint were absent. Silently accepting it would let a stale selector or a
/// hand-built lane ship a word whose width fields were never checked against
/// the operand the hint described.
#[test]
fn function_encoder_refuses_legacy_width_hint_operand_at_index_2() {
    for (opcode, source, hint) in [
        (AArch64Opcode::FcvtzsRR, S0, 32),
        (AArch64Opcode::FcvtzsRR, D0, 64),
        (AArch64Opcode::FcvtzuRR, S0, 32),
        (AArch64Opcode::FcvtzuRR, D0, 64),
    ] {
        for destination in [W0, X0] {
            let signature = Signature::new(vec![MachType::F64], vec![MachType::I64]);
            let mut func = MachFunction::new("legacy_hint".to_string(), signature);
            let entry = func.entry;
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(destination),
                    MachOperand::PReg(source),
                    MachOperand::Imm(hint),
                ],
            );
            let id = func.push_inst(inst);
            func.append_inst(entry, id);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]);
            let ret_id = func.push_inst(ret);
            func.append_inst(entry, ret_id);

            let error = encode_function(&func)
                .expect_err("a third conversion operand has no encoding and must be refused");
            let text = error.to_string();
            assert!(
                text.contains("index 2") && text.contains(&format!("{opcode:?}")),
                "{opcode:?} {destination:?}: error must name operand index 2, got {text}"
            );
            assert!(
                text.contains("exactly two register operands"),
                "{opcode:?} {destination:?}: unexpected error text {text}"
            );

            // The same instruction with the hint removed is the canonical
            // shape and encodes.
            let mut canonical = MachFunction::new(
                "canonical".to_string(),
                Signature::new(vec![MachType::F64], vec![MachType::I64]),
            );
            let entry = canonical.entry;
            let inst = MachInst::new(
                opcode,
                vec![MachOperand::PReg(destination), MachOperand::PReg(source)],
            );
            let id = canonical.push_inst(inst);
            canonical.append_inst(entry, id);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]);
            let ret_id = canonical.push_inst(ret);
            canonical.append_inst(entry, ret_id);
            let code = encode_function(&canonical).unwrap();
            let word = le_u32(&code, 0);
            let sf_64 = destination == X0;
            let ftype = u32::from(source == D0);
            assert_eq!(
                word & !REGISTER_FIELDS,
                expected_fcvtz(sf_64, ftype, opcode == AArch64Opcode::FcvtzuRR),
                "{opcode:?} {destination:?} {source:?}: canonical word {word:08x}"
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
