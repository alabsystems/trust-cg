// trust-cg-codegen/tests/x86_64_coff_constant_pool.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::coff::{
    IMAGE_FILE_MACHINE_AMD64, IMAGE_REL_AMD64_REL32, IMAGE_SYM_CLASS_EXTERNAL,
    IMAGE_SYM_CLASS_STATIC, IMAGE_SYM_TYPE_NULL,
};
use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{
    X86ISelConstPoolEntry, X86ISelFunction, X86ISelInst, X86ISelOperand,
};

fn read_u16(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn short_name(bytes: &[u8], offset: usize) -> &str {
    let name = &bytes[offset..offset + 8];
    let len = name.iter().position(|&byte| byte == 0).unwrap_or(8);
    std::str::from_utf8(&name[..len]).unwrap()
}

fn global_ref_function(symbol: &str) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let entry = Block(0);
    let mut func = X86ISelFunction::new("mat".to_string(), sig);
    func.ensure_block(entry);
    let dst = VReg::new(0, RegClass::Gpr64);
    func.next_vreg = 1;
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::LeaRip,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::Symbol(symbol.to_string()),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn extern_ref_function(symbol: &str) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let entry = Block(0);
    let mut func = X86ISelFunction::new("mat_ext".to_string(), sig);
    func.ensure_block(entry);
    let dst = VReg::new(0, RegClass::Gpr64);
    func.next_vreg = 1;
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRipRel,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::Symbol(symbol.to_string()),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

#[test]
fn single_function_coff_emits_rdata_rel32_for_movsd_constant_pool() {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut func = X86ISelFunction::new("cp".to_string(), sig);
    let entry = Block(0);
    func.ensure_block(entry);
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: 1.25f64.to_le_bytes().to_vec(),
        align: 8,
    });

    let dst = VReg::new(0, RegClass::Fpr64);
    func.next_vreg = 1;
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::ConstPoolEntry(0)],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    });
    let bytes = pipeline.compile_function(&func).unwrap();

    assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
    assert_eq!(read_u16(&bytes, 2), 2, "expected .text and .rdata");
    assert_eq!(
        read_u32(&bytes, 12),
        2,
        "expected function and .rdata symbols"
    );

    let text_header = 20;
    let rdata_header = text_header + 40;
    assert_eq!(&bytes[text_header..text_header + 5], b".text");
    assert_eq!(&bytes[rdata_header..rdata_header + 6], b".rdata");

    let text_raw = read_u32(&bytes, text_header + 20) as usize;
    let text_size = read_u32(&bytes, text_header + 16) as usize;
    let text_reloc_ptr = read_u32(&bytes, text_header + 24) as usize;
    assert_eq!(read_u16(&bytes, text_header + 32), 1);

    let rdata_raw = read_u32(&bytes, rdata_header + 20) as usize;
    let rdata_size = read_u32(&bytes, rdata_header + 16) as usize;
    assert_eq!(rdata_size, 8);
    assert_eq!(&bytes[rdata_raw..rdata_raw + 8], &1.25f64.to_le_bytes());

    let reloc_va = read_u32(&bytes, text_reloc_ptr) as usize;
    let reloc_sym = read_u32(&bytes, text_reloc_ptr + 4);
    assert_eq!(read_u16(&bytes, text_reloc_ptr + 8), IMAGE_REL_AMD64_REL32);
    assert_eq!(reloc_sym, 1, "relocation should target .rdata symbol");
    assert!(reloc_va + 4 <= text_size);
    assert_eq!(
        read_u32(&bytes, text_raw + reloc_va),
        0,
        "first constant-pool entry should use a section-relative addend, not stale inline RIP displacement"
    );

    let symtab = read_u32(&bytes, 8) as usize;
    let rdata_symbol = symtab + 18;
    assert_eq!(&bytes[rdata_symbol..rdata_symbol + 6], b".rdata");
    assert_eq!(read_u16(&bytes, rdata_symbol + 12), 2);
    assert_eq!(read_u16(&bytes, rdata_symbol + 14), IMAGE_SYM_TYPE_NULL);
    assert_eq!(bytes[rdata_symbol + 16], IMAGE_SYM_CLASS_STATIC);
}

#[test]
fn module_coff_lifts_constant_pools_to_rdata_and_preserves_call_relocation() {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let entry = Block(0);

    let mut caller = X86ISelFunction::new("caller".to_string(), sig.clone());
    caller.ensure_block(entry);
    caller.const_pool_entries.push(X86ISelConstPoolEntry {
        data: 3.5f32.to_le_bytes().to_vec(),
        align: 4,
    });
    let caller_dst = VReg::new(0, RegClass::Fpr32);
    caller.next_vreg = 1;
    caller.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovssRipRel,
            vec![
                X86ISelOperand::VReg(caller_dst),
                X86ISelOperand::ConstPoolEntry(0),
            ],
        ),
    );
    caller.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("callee".to_string())],
        ),
    );
    caller.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    let mut callee = X86ISelFunction::new("callee".to_string(), sig);
    callee.ensure_block(entry);
    callee.const_pool_entries.push(X86ISelConstPoolEntry {
        data: 6.25f64.to_le_bytes().to_vec(),
        align: 8,
    });
    let callee_dst = VReg::new(0, RegClass::Fpr64);
    callee.next_vreg = 1;
    callee.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![
                X86ISelOperand::VReg(callee_dst),
                X86ISelOperand::ConstPoolEntry(0),
            ],
        ),
    );
    callee.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    });
    let bytes = pipeline.compile_module(&[caller, callee]).unwrap();

    assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
    assert_eq!(read_u16(&bytes, 2), 2, "expected .text and .rdata");
    assert_eq!(read_u32(&bytes, 12), 3, "expected two functions and .rdata");

    let text_header = 20;
    let rdata_header = text_header + 40;
    assert_eq!(short_name(&bytes, text_header), ".text");
    assert_eq!(short_name(&bytes, rdata_header), ".rdata");

    let text_raw = read_u32(&bytes, text_header + 20) as usize;
    let text_size = read_u32(&bytes, text_header + 16) as usize;
    let text_reloc_ptr = read_u32(&bytes, text_header + 24) as usize;
    assert_eq!(read_u16(&bytes, text_header + 32), 3);

    let rdata_raw = read_u32(&bytes, rdata_header + 20) as usize;
    let rdata_size = read_u32(&bytes, rdata_header + 16) as usize;
    assert_eq!(rdata_size, 16);
    assert_eq!(&bytes[rdata_raw..rdata_raw + 4], &3.5f32.to_le_bytes());
    assert_eq!(&bytes[rdata_raw + 4..rdata_raw + 8], &[0, 0, 0, 0]);
    assert_eq!(
        &bytes[rdata_raw + 8..rdata_raw + 16],
        &6.25f64.to_le_bytes()
    );

    let symtab = read_u32(&bytes, 8) as usize;
    assert_eq!(short_name(&bytes, symtab), "caller");
    assert_eq!(short_name(&bytes, symtab + 18), "callee");
    assert_eq!(short_name(&bytes, symtab + 36), ".rdata");
    assert_eq!(read_u16(&bytes, symtab + 36 + 12), 2);
    assert_eq!(read_u16(&bytes, symtab + 36 + 14), IMAGE_SYM_TYPE_NULL);
    assert_eq!(bytes[symtab + 36 + 16], IMAGE_SYM_CLASS_STATIC);

    let mut rdata_addends = Vec::new();
    let mut saw_call_relocation = false;
    for reloc_idx in 0..3 {
        let reloc = text_reloc_ptr + reloc_idx * 10;
        let reloc_va = read_u32(&bytes, reloc) as usize;
        let reloc_sym = read_u32(&bytes, reloc + 4);
        assert_eq!(read_u16(&bytes, reloc + 8), IMAGE_REL_AMD64_REL32);
        assert!(reloc_va + 4 <= text_size);
        let addend = read_u32(&bytes, text_raw + reloc_va);
        match reloc_sym {
            1 => {
                assert_eq!(addend, 0, "CALL rel32 relocation keeps a zero addend");
                saw_call_relocation = true;
            }
            2 => rdata_addends.push(addend),
            other => panic!("unexpected relocation symbol index {other}"),
        }
    }

    rdata_addends.sort_unstable();
    assert_eq!(rdata_addends, vec![0, 8]);
    assert!(saw_call_relocation, "expected call relocation to callee");
}

#[test]
fn module_coff_emits_rel32_global_ref_relocation_to_defined_symbol() {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let entry = Block(0);
    let materialize = global_ref_function("callee");

    let mut callee = X86ISelFunction::new("callee".to_string(), sig);
    callee.ensure_block(entry);
    callee.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    });
    let bytes = pipeline.compile_module(&[materialize, callee]).unwrap();

    assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
    assert_eq!(read_u16(&bytes, 2), 1, "expected only .text");
    assert_eq!(read_u32(&bytes, 12), 2, "expected two function symbols");

    let text_header = 20;
    assert_eq!(short_name(&bytes, text_header), ".text");
    let text_raw = read_u32(&bytes, text_header + 20) as usize;
    let text_size = read_u32(&bytes, text_header + 16) as usize;
    let text_reloc_ptr = read_u32(&bytes, text_header + 24) as usize;
    assert_eq!(read_u16(&bytes, text_header + 32), 1);

    let symtab = read_u32(&bytes, 8) as usize;
    assert_eq!(short_name(&bytes, symtab), "mat");
    assert_eq!(short_name(&bytes, symtab + 18), "callee");

    let reloc_va = read_u32(&bytes, text_reloc_ptr) as usize;
    let reloc_sym = read_u32(&bytes, text_reloc_ptr + 4);
    assert_eq!(read_u16(&bytes, text_reloc_ptr + 8), IMAGE_REL_AMD64_REL32);
    assert_eq!(reloc_va, 3);
    assert_eq!(reloc_sym, 1, "GlobalRef relocation should target callee");
    assert!(reloc_va + 4 <= text_size);
    assert_eq!(
        read_u32(&bytes, text_raw + reloc_va),
        0,
        "GlobalRef REL32 relocation should keep a zero addend"
    );
}

#[test]
fn module_coff_emits_rel32_extern_ref_relocation_to_import_symbol() {
    let materialize = extern_ref_function("a");

    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    });
    let bytes = pipeline.compile_module(&[materialize]).unwrap();

    assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
    assert_eq!(read_u16(&bytes, 2), 1, "expected only .text");
    assert_eq!(
        read_u32(&bytes, 12),
        2,
        "expected function and import symbols"
    );

    let text_header = 20;
    assert_eq!(short_name(&bytes, text_header), ".text");
    let text_raw = read_u32(&bytes, text_header + 20) as usize;
    let text_size = read_u32(&bytes, text_header + 16) as usize;
    let text_reloc_ptr = read_u32(&bytes, text_header + 24) as usize;
    assert_eq!(read_u16(&bytes, text_header + 32), 1);

    let symtab = read_u32(&bytes, 8) as usize;
    assert_eq!(short_name(&bytes, symtab), "mat_ext");
    let import_symbol = symtab + 18;
    assert_eq!(short_name(&bytes, import_symbol), "__imp_a");
    assert_eq!(read_u16(&bytes, import_symbol + 12), 0);
    assert_eq!(read_u16(&bytes, import_symbol + 14), IMAGE_SYM_TYPE_NULL);
    assert_eq!(bytes[import_symbol + 16], IMAGE_SYM_CLASS_EXTERNAL);

    let reloc_va = read_u32(&bytes, text_reloc_ptr) as usize;
    let reloc_sym = read_u32(&bytes, text_reloc_ptr + 4);
    assert_eq!(read_u16(&bytes, text_reloc_ptr + 8), IMAGE_REL_AMD64_REL32);
    assert_eq!(reloc_va, 3);
    assert_eq!(reloc_sym, 1, "ExternRef relocation should target __imp_a");
    assert!(reloc_va + 4 <= text_size);
    assert_eq!(
        read_u32(&bytes, text_raw + reloc_va),
        0,
        "ExternRef REL32 relocation should keep a zero addend"
    );
}
