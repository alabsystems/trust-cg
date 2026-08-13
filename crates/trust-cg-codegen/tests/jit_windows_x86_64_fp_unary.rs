#![cfg(all(target_arch = "x86_64", target_os = "windows"))]

use std::ffi::c_void;

use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::X86CallAbi;
use trust_cg_regalloc::AllocStrategy;

const MEM_COMMIT: u32 = 0x1000;
const MEM_RESERVE: u32 = 0x2000;
const MEM_RELEASE: u32 = 0x8000;
const PAGE_READWRITE: u32 = 0x04;
const PAGE_EXECUTE_READ: u32 = 0x20;

unsafe extern "system" {
    fn VirtualAlloc(
        lp_address: *mut c_void,
        dw_size: usize,
        fl_allocation_type: u32,
        fl_protect: u32,
    ) -> *mut c_void;
    fn VirtualProtect(
        lp_address: *mut c_void,
        dw_size: usize,
        fl_new_protect: u32,
        lpfl_old_protect: *mut u32,
    ) -> i32;
    fn VirtualFree(lp_address: *mut c_void, dw_size: usize, dw_free_type: u32) -> i32;
}

struct ExecutablePage {
    ptr: *mut c_void,
}

impl ExecutablePage {
    fn publish(code: &[u8]) -> Self {
        assert!(!code.is_empty(), "cannot publish empty code");
        let ptr = unsafe {
            VirtualAlloc(
                std::ptr::null_mut(),
                code.len(),
                MEM_COMMIT | MEM_RESERVE,
                PAGE_READWRITE,
            )
        };
        assert!(!ptr.is_null(), "VirtualAlloc failed for JIT smoke buffer");

        unsafe {
            std::ptr::copy_nonoverlapping(code.as_ptr(), ptr.cast::<u8>(), code.len());
        }

        let mut old_protect = 0_u32;
        let ok = unsafe { VirtualProtect(ptr, code.len(), PAGE_EXECUTE_READ, &mut old_protect) };
        assert_ne!(ok, 0, "VirtualProtect failed for JIT smoke buffer");

        Self { ptr }
    }

    fn as_f64_to_f64(&self) -> extern "C" fn(f64) -> f64 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_f64_to_i32(&self) -> extern "C" fn(f64) -> i32 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_i64_to_i64(&self) -> extern "C" fn(i64) -> i64 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_i64_i64_i64_i64_to_i64(&self) -> extern "C" fn(i64, i64, i64, i64) -> i64 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_i64_i64_to_i64(&self) -> extern "C" fn(i64, i64) -> i64 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_i32_i32_to_i32(&self) -> extern "C" fn(i32, i32) -> i32 {
        unsafe { std::mem::transmute(self.ptr) }
    }

    fn as_i64_i64_i32_i32_to_i32(&self) -> extern "C" fn(i64, i64, i32, i32) -> i32 {
        unsafe { std::mem::transmute(self.ptr) }
    }
}

impl Drop for ExecutablePage {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe {
                VirtualFree(self.ptr, 0, MEM_RELEASE);
            }
        }
    }
}

fn scalar_fabs_fsqrt_f64_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "sqrt_abs_f64",
        Signature {
            params: vec![Type::F64],
            returns: vec![Type::F64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Fabs,
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Fsqrt,
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_bitcast_f64_to_i64_trunc_i32_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "bitcast_trunc_f64_i32",
        Signature {
            params: vec![Type::F64],
            returns: vec![Type::I32],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Bitcast { to_ty: Type::I64 },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Trunc { to_ty: Type::I32 },
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_select_i64_from_icmp_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "select_i64_from_icmp",
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::SignedGreaterThan,
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Select {
                        cond: IntCC::NotEqual,
                    },
                    args: vec![Value(4), Value(2), Value(3)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(5)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_select_i32_from_icmp_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "select_i32_from_icmp",
        Signature {
            params: vec![Type::I64, Type::I64, Type::I32, Type::I32],
            returns: vec![Type::I32],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::SignedGreaterThan,
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Select {
                        cond: IntCC::NotEqual,
                    },
                    args: vec![Value(4), Value(2), Value(3)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(5)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn checked_i64_overflow_flag_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2), Value(3)],
                },
                Instruction {
                    opcode: Opcode::Uextend {
                        from_ty: Type::B1,
                        to_ty: Type::I64,
                    },
                    args: vec![Value(3)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(4)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn checked_umul_value_plus_flag_lir(name: &str, ty: Type) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::CheckedUmul,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2), Value(3)],
                },
                Instruction {
                    opcode: Opcode::Uextend {
                        from_ty: Type::B1,
                        to_ty: ty,
                    },
                    args: vec![Value(3)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![Value(2), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(5)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_binary_not_i64_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_binary_not_b1_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Icmp { cond: IntCC::Equal },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::SignedGreaterThan,
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode,
                    args: vec![Value(2), Value(3)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Uextend {
                        from_ty: Type::B1,
                        to_ty: Type::I64,
                    },
                    args: vec![Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(5)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_bitfield_extract_i64_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode,
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_bitfield_insert_i64_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "insert_mid12_i64",
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::InsertBits { lsb: 16, width: 12 },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn scalar_bitfield_insert_i64_alias_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "insert_mid12_i64_alias",
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::InsertBits { lsb: 16, width: 12 },
                    args: vec![Value(0), Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

#[test]
fn x86_64_windows_jit_scalar_fabs_fsqrt_f64_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });
    let code = pipeline
        .compile_trust_ir_function(&scalar_fabs_fsqrt_f64_lir())
        .expect("x86-64 pipeline should compile scalar fabs/fsqrt LIR");
    let page = ExecutablePage::publish(&code);
    let sqrt_abs = page.as_f64_to_f64();

    assert_eq!(sqrt_abs(-9.0), 3.0);
    assert_eq!(sqrt_abs(16.0), 4.0);
    assert_eq!(sqrt_abs(-0.0).to_bits(), 0.0_f64.to_bits());
    assert!(sqrt_abs(f64::NAN).is_nan());
}

#[test]
fn x86_64_windows_jit_scalar_bitcast_f64_to_i64_trunc_i32_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });
    let code = pipeline
        .compile_trust_ir_function(&scalar_bitcast_f64_to_i64_trunc_i32_lir())
        .expect("x86-64 pipeline should compile scalar bitcast/trunc LIR");
    let page = ExecutablePage::publish(&code);
    let low32 = page.as_f64_to_i32();

    assert_eq!(
        low32(f64::from_bits(0x3ff0_0000_dead_beef)),
        0xdead_beefu32 as i32
    );
    assert_eq!(low32(f64::from_bits(0x4008_0000_1122_3344)), 0x1122_3344);
}

#[test]
fn x86_64_windows_jit_scalar_select_i64_from_icmp_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });
    let code = pipeline
        .compile_trust_ir_function(&scalar_select_i64_from_icmp_lir())
        .expect("x86-64 pipeline should compile scalar select LIR");
    let page = ExecutablePage::publish(&code);
    let select = page.as_i64_i64_i64_i64_to_i64();

    assert_eq!(select(9, 4, 44, 55), 44);
    assert_eq!(select(4, 9, 44, 55), 55);
    assert_eq!(select(-3, -7, -11, 22), -11);
}

#[test]
fn x86_64_windows_jit_scalar_select_i32_from_icmp_full_regalloc_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });
    let code = pipeline
        .compile_trust_ir_function(&scalar_select_i32_from_icmp_lir())
        .expect("x86-64 pipeline should compile scalar i32 select LIR");
    let page = ExecutablePage::publish(&code);
    let select = page.as_i64_i64_i32_i32_to_i32();

    assert_eq!(select(9, 4, 44, 55), 44);
    assert_eq!(select(4, 9, 44, 55), 55);
    assert_eq!(select(-3, -7, -11, 22), -11);
}

#[test]
fn x86_64_windows_jit_checked_i64_overflow_flags_full_regalloc_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });

    for (name, opcode, overflow_case, no_overflow_case) in [
        (
            "checked_sadd_i64_flag",
            Opcode::CheckedSadd,
            (i64::MAX, 1),
            (40, 2),
        ),
        (
            "checked_ssub_i64_flag",
            Opcode::CheckedSsub,
            (i64::MIN, 1),
            (40, 2),
        ),
        (
            "checked_smul_i64_flag",
            Opcode::CheckedSmul,
            (i64::MAX, 2),
            (21, 2),
        ),
        (
            "checked_uadd_i64_flag",
            Opcode::CheckedUadd,
            (-1, 1),
            (40, 2),
        ),
        (
            "checked_usub_i64_flag",
            Opcode::CheckedUsub,
            (0, 1),
            (40, 2),
        ),
        (
            "checked_umul_i64_flag",
            Opcode::CheckedUmul,
            (-1, 2),
            (21, 2),
        ),
    ] {
        let code = pipeline
            .compile_trust_ir_function(&checked_i64_overflow_flag_lir(name, opcode))
            .unwrap_or_else(|err| panic!("x86-64 pipeline should compile {name}: {err}"));
        let page = ExecutablePage::publish(&code);
        let overflow_flag = page.as_i64_i64_to_i64();

        assert_eq!(overflow_flag(overflow_case.0, overflow_case.1), 1, "{name}");
        assert_eq!(
            overflow_flag(no_overflow_case.0, no_overflow_case.1),
            0,
            "{name}"
        );
    }
}

#[test]
fn x86_64_windows_jit_checked_umul_value_survives_flag_materialization() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });

    let code = pipeline
        .compile_trust_ir_function(&checked_umul_value_plus_flag_lir(
            "checked_umul_i64_value_plus_flag",
            Type::I64,
        ))
        .expect("x86-64 pipeline should compile checked i64 unsigned multiply value smoke");
    let page = ExecutablePage::publish(&code);
    let checked_umul_i64 = page.as_i64_i64_to_i64();
    assert_eq!(checked_umul_i64(-1, 2), -1);
    assert_eq!(checked_umul_i64(21, 2), 42);

    let code = pipeline
        .compile_trust_ir_function(&checked_umul_value_plus_flag_lir(
            "checked_umul_i32_value_plus_flag",
            Type::I32,
        ))
        .expect("x86-64 pipeline should compile checked i32 unsigned multiply value smoke");
    let page = ExecutablePage::publish(&code);
    let checked_umul_i32 = page.as_i32_i32_to_i32();
    assert_eq!(checked_umul_i32(-1, 2), -1);
    assert_eq!(checked_umul_i32(21, 2), 42);
}

#[test]
fn x86_64_windows_jit_scalar_bandnot_bornot_i64_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });

    let code = pipeline
        .compile_trust_ir_function(&scalar_binary_not_i64_lir("bandnot_i64", Opcode::BandNot))
        .expect("x86-64 pipeline should compile i64 BandNot");
    let page = ExecutablePage::publish(&code);
    let bandnot = page.as_i64_i64_to_i64();
    assert_eq!(bandnot(0xff, 0x0f), 0xf0);
    assert_eq!(bandnot(-1, 0xff), !0xff_i64);

    let code = pipeline
        .compile_trust_ir_function(&scalar_binary_not_i64_lir("bornot_i64", Opcode::BorNot))
        .expect("x86-64 pipeline should compile i64 BorNot");
    let page = ExecutablePage::publish(&code);
    let bornot = page.as_i64_i64_to_i64();
    assert_eq!(bornot(0, -1), 0);
    assert_eq!(bornot(0, 0), -1);
    assert_eq!(bornot(0x0f, 0xf0), !0xf0_i64 | 0x0f);
}

#[test]
fn x86_64_windows_jit_scalar_bandnot_bornot_b1_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });

    let code = pipeline
        .compile_trust_ir_function(&scalar_binary_not_b1_lir("bandnot_b1", Opcode::BandNot))
        .expect("x86-64 pipeline should compile B1 BandNot");
    let page = ExecutablePage::publish(&code);
    let bandnot = page.as_i64_i64_to_i64();
    assert_eq!(bandnot(5, 5), 1);
    assert_eq!(bandnot(7, 3), 0);
    assert_eq!(bandnot(3, 7), 0);

    let code = pipeline
        .compile_trust_ir_function(&scalar_binary_not_b1_lir("bornot_b1", Opcode::BorNot))
        .expect("x86-64 pipeline should compile B1 BorNot");
    let page = ExecutablePage::publish(&code);
    let bornot = page.as_i64_i64_to_i64();
    assert_eq!(bornot(5, 5), 1);
    assert_eq!(bornot(7, 3), 0);
    assert_eq!(bornot(3, 7), 1);
}

#[test]
fn x86_64_windows_jit_scalar_bitfield_i64_smoke() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Full(AllocStrategy::Greedy),
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    });

    let code = pipeline
        .compile_trust_ir_function(&scalar_bitfield_extract_i64_lir(
            "extract_mid16_i64",
            Opcode::ExtractBits { lsb: 8, width: 16 },
        ))
        .expect("x86-64 pipeline should compile i64 ExtractBits");
    let page = ExecutablePage::publish(&code);
    let extract = page.as_i64_to_i64();
    assert_eq!(extract(0x1234_5678_9abc_def0), 0xbcde);
    assert_eq!(extract(-1), 0xffff);
    assert_eq!(extract(0xff), 0);

    let code = pipeline
        .compile_trust_ir_function(&scalar_bitfield_extract_i64_lir(
            "sextract_mid12_i64",
            Opcode::SextractBits { lsb: 4, width: 12 },
        ))
        .expect("x86-64 pipeline should compile i64 SextractBits");
    let page = ExecutablePage::publish(&code);
    let sextract = page.as_i64_to_i64();
    assert_eq!(sextract(0x8000), -2048);
    assert_eq!(sextract(0x7ff0), 2047);
    assert_eq!(sextract(0xfab0), -85);

    let code = pipeline
        .compile_trust_ir_function(&scalar_bitfield_insert_i64_lir())
        .expect("x86-64 pipeline should compile i64 InsertBits");
    let page = ExecutablePage::publish(&code);
    let insert = page.as_i64_i64_to_i64();
    assert_eq!(insert(0x1234_5678_9abc_def0, 0xfed), 0x1234_5678_9fed_def0);
    assert_eq!(insert(-1, 0), 0xffff_ffff_f000_ffff_u64 as i64);

    let code = pipeline
        .compile_trust_ir_function(&scalar_bitfield_insert_i64_alias_lir())
        .expect("x86-64 pipeline should compile aliased i64 InsertBits");
    let page = ExecutablePage::publish(&code);
    let insert_alias = page.as_i64_to_i64();
    assert_eq!(insert_alias(0x1234_5678_9abc_def0), 0x1234_5678_9ef0_def0);
}
