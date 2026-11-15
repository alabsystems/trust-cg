// trust-cg-codegen/tests/x86_64_bool_not_abi.rs - a negated `bool` is a clean 32-bit bool at the ABI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The x86-64 backend's `B1` is a clean 32-bit bool (0 or 1) wherever it is
//! defined: it is returned in EAX and passed as a 32-bit call argument, which
//! an LLVM callee of a `bool` argument reads whole, and every `B1` consumer
//! (`movzx` for a zero extension, `test` for a branch) reads it as 0/1.
//!
//! Two producers broke that, measured with every register filled with `0xA5`
//! bytes before the call:
//!
//! * a LIR `Bnot` of a `B1` was a bare `not r32`, so `!true` returned
//!   EAX=0xFFFFFFFE and `(!b) as u32` was 254/255. The selector now masks the
//!   result to bit 0 (`not`, then `and` with 1), as it already did for a `B1`
//!   `BandNot`/`BorNot`.
//! * trust-ir `not bool` and `bitcast u8 -> bool` reached that `Bnot` and a
//!   plain register move into a `B1` through the lanes that run no validation
//!   (the AOT `Compiler::compile`, which the trust-cg CLI calls). trust-ir
//!   states both invalid; the adapter refuses them, and the x86-64 selector
//!   refuses a `Bitcast` into `B1` from anything but a `B1`.
//!
//! Legs, each at O0 and O2 through `X86Pipeline`:
//!
//! * host-neutral: after the production x86 pass order, the register moved
//!   into EAX before `RET` and into EDI before `CALL` is an `and` with 1 of
//!   the `not`, so no pass deleted the mask;
//! * native (an x86-64 host that links and runs x86-64): the object is linked
//!   against a C driver whose trampoline fills every general-purpose register
//!   with `0xA5` bytes before the call, and EAX / the callee's EDI must be
//!   exactly 0 or 1.

mod common;

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::fs;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};
use common::x86_64_object::{HOST_IS_MACHO, assert_host_x86_64_object};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{EAX, EDI, X86PReg};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelFunction, X86ISelInst, X86ISelOperand, X86InstructionSelector,
};
use trust_cg_opt::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, CastOp, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, UnOp, ValueId,
};

const OPT_LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// The C callee: returns its whole 32-bit argument register.
const SINK: &str = "_bool_sink";
const NOT_RET: &str = "_tcg_b1_not_ret";
const NOT_PASS: &str = "_tcg_b1_not_pass";
const NOT_ZEXT: &str = "_tcg_b1_not_zext";

fn bnot(src: u32, dst: u32) -> Instruction {
    Instruction {
        opcode: Opcode::Bnot,
        args: vec![Value(src)],
        results: vec![Value(dst)],
    }
}

fn ret(value: u32) -> Instruction {
    Instruction {
        opcode: Opcode::Return,
        args: vec![Value(value)],
        results: vec![],
    }
}

/// `name(b: B1) -> returns { instructions }`, the parameter as `Value(0)`.
fn lir_function(name: &str, returns: Type, instructions: Vec<Instruction>) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::B1],
            returns: vec![returns],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

/// `!b`, `sink(!b)` and `(!b) as u32`, with the value types the adapter would
/// seed.
fn lir_functions() -> Vec<(LirFunction, Vec<(Value, Type)>)> {
    vec![
        (
            lir_function(NOT_RET, Type::B1, vec![bnot(0, 1), ret(1)]),
            vec![(Value(0), Type::B1), (Value(1), Type::B1)],
        ),
        (
            lir_function(
                NOT_PASS,
                Type::I32,
                vec![
                    bnot(0, 1),
                    Instruction {
                        opcode: Opcode::Call {
                            name: SINK.to_owned(),
                            binding: Default::default(),
                        },
                        args: vec![Value(1)],
                        results: vec![Value(2)],
                    },
                    ret(2),
                ],
            ),
            vec![
                (Value(0), Type::B1),
                (Value(1), Type::B1),
                (Value(2), Type::I32),
            ],
        ),
        (
            lir_function(
                NOT_ZEXT,
                Type::I32,
                vec![
                    bnot(0, 1),
                    Instruction {
                        opcode: Opcode::Uextend {
                            from_ty: Type::B1,
                            to_ty: Type::I32,
                        },
                        args: vec![Value(1)],
                        results: vec![Value(2)],
                    },
                    ret(2),
                ],
            ),
            vec![
                (Value(0), Type::B1),
                (Value(1), Type::B1),
                (Value(2), Type::I32),
            ],
        ),
    ]
}

/// The real x86-64 instruction selector, System V.
fn select(func: &LirFunction, value_types: &[(Value, Type)]) -> X86ISelFunction {
    let mut isel = X86InstructionSelector::with_abi(
        func.name.clone(),
        func.signature.clone(),
        X86CallAbi::SystemV,
    );
    isel.seed_value_types(&value_types.iter().cloned().collect());
    isel.seed_function_value_use_counts(func);
    isel.lower_formal_arguments(&func.signature, func.entry_block)
        .unwrap_or_else(|error| panic!("{}: formal arguments: {error:?}", func.name));
    isel.select_block(
        func.entry_block,
        &func.blocks[&func.entry_block].instructions,
    )
    .unwrap_or_else(|error| panic!("{}: selection: {error:?}", func.name));
    isel.finalize()
}

fn pipeline(opt_level: OptLevel, output_format: X86OutputFormat) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level,
        output_format,
        ..X86PipelineConfig::default()
    })
}

fn entry(func: &X86ISelFunction) -> &[X86ISelInst] {
    &func.blocks[&Block(0)].insts
}

/// The last instruction before `before` that names `reg` in operand 0.
fn definition(insts: &[X86ISelInst], before: usize, reg: VReg) -> Option<usize> {
    insts[..before]
        .iter()
        .rposition(|inst| inst.operands.first() == Some(&X86ISelOperand::VReg(reg)))
}

fn is_one(insts: &[X86ISelInst], before: usize, operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::Imm(1) => true,
        X86ISelOperand::VReg(reg) => definition(insts, before, *reg).is_some_and(|def| {
            insts[def].opcode == X86Opcode::MovRI
                && insts[def].operands.get(1) == Some(&X86ISelOperand::Imm(1))
        }),
        _ => false,
    }
}

fn is_not(insts: &[X86ISelInst], before: usize, operand: &X86ISelOperand) -> bool {
    let X86ISelOperand::VReg(reg) = operand else {
        return false;
    };
    definition(insts, before, *reg).is_some_and(|def| insts[def].opcode == X86Opcode::Not)
}

/// Whether the register `reg` read at `before` is an `and` with 1 of a `not`,
/// following register copies back.
fn is_masked_not(insts: &[X86ISelInst], before: usize, reg: VReg) -> bool {
    let (mut at, mut cur) = (before, reg);
    loop {
        let Some(def) = definition(insts, at, cur) else {
            return false;
        };
        let inst = &insts[def];
        match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::MovRR | X86Opcode::MovRR32, [_, X86ISelOperand::VReg(src)]) => {
                (at, cur) = (def, *src);
            }
            (X86Opcode::AndRR | X86Opcode::AndRI, [_, lhs, rhs]) => {
                return (is_one(insts, def, rhs) && is_not(insts, def, lhs))
                    || (is_one(insts, def, lhs) && is_not(insts, def, rhs));
            }
            _ => return false,
        }
    }
}

/// The register copied into `preg` last before the first `opcode`.
fn copied_into_before(insts: &[X86ISelInst], preg: X86PReg, opcode: X86Opcode) -> (usize, VReg) {
    let site = insts
        .iter()
        .position(|inst| inst.opcode == opcode)
        .unwrap_or_else(|| panic!("no {opcode:?}: {insts:#?}"));
    let copy = insts[..site]
        .iter()
        .rposition(|inst| inst.operands.first() == Some(&X86ISelOperand::PReg(preg)))
        .unwrap_or_else(|| panic!("nothing written to {preg:?} before {opcode:?}: {insts:#?}"));
    match insts[copy].operands.get(1) {
        Some(X86ISelOperand::VReg(src)) => (copy, *src),
        other => panic!("{preg:?} is written from {other:?}: {insts:#?}"),
    }
}

#[test]
fn negated_bools_are_masked_before_every_abi_boundary_after_the_x86_passes() {
    for opt_level in OPT_LEVELS {
        for (func, value_types) in lir_functions() {
            let (preg, boundary) = match func.name.as_str() {
                NOT_RET => (EAX, X86Opcode::Ret),
                NOT_PASS => (EDI, X86Opcode::Call),
                _ => continue,
            };
            let mut selected = select(&func, &value_types);
            let _ = pipeline(opt_level, X86OutputFormat::RawBytes)
                .run_x86_optimization_passes(&mut selected);
            let insts = entry(&selected);
            let (copy, src) = copied_into_before(insts, preg, boundary);
            assert!(
                is_masked_not(insts, copy, src),
                "{} at {opt_level:?}: the bool reaching {preg:?} before {boundary:?} is not \
                 masked to bit 0: {insts:#?}",
                func.name
            );
        }
    }
}

/// The driver's trampoline fills every general-purpose register other than
/// RSP/RBP with `0xA5` bytes (the bool argument keeps only its low byte),
/// calls, and hands back RAX whole. System V: entry RSP is 8 mod 16; the six
/// pushes and one more 8-byte slot align it for the call.
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

#if defined(__APPLE__)
#define SYM(name) "_" #name
#else
#define SYM(name) #name
#endif

#define DIRTY "$0xa5a5a5a5a5a5a5a5"

#define FILL_SCRATCH                                                        \
    "  movabsq " DIRTY ", %rax\n"                                           \
    "  movq %rax, %rbx\n  movq %rax, %rcx\n  movq %rax, %rdx\n"               \
    "  movq %rax, %r8\n  movq %rax, %r9\n  movq %rax, %r10\n"                 \
    "  movq %rax, %r12\n  movq %rax, %r13\n  movq %rax, %r14\n"               \
    "  movq %rax, %r15\n"

/* uint64_t call_dirty(void *fn, uint64_t b): fn(b) with bits 32..63 of RDI
   and every other register dirty. A caller passing a `bool` sets EDI to 0/1
   (clang zero-extends it to 32 bits), so only RDI's upper half is dirty. */
__asm__(
    ".text\n"
    ".globl " SYM(call_dirty) "\n"
    SYM(call_dirty) ":\n"
    "  pushq %rbp\n  movq %rsp, %rbp\n"
    "  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
    "  subq $8, %rsp\n"
    "  movq %rdi, %r11\n"
    "  movabsq $0xa5a5a5a500000000, %rdi\n  orq %rsi, %rdi\n"
    "  movabsq " DIRTY ", %rsi\n"
    FILL_SCRATCH
    "  callq *%r11\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n"
    "  popq %rbp\n  retq\n");

uint64_t call_dirty(void *fn, uint64_t b);

extern unsigned char _tcg_b1_not_ret(unsigned char);
extern unsigned _tcg_b1_not_pass(unsigned char);
extern unsigned _tcg_b1_not_zext(unsigned char);

/* The callee reads its whole 32-bit argument register, as an LLVM callee of a
   `bool` argument does. */
unsigned _bool_sink(unsigned b) { return b; }

static int failures = 0;

static void check(const char *what, unsigned b, uint64_t rax) {
    uint32_t eax = (uint32_t)rax;
    printf("%s(%u) eax=0x%08x\n", what, b, eax);
    if (eax != !b) failures++;
}

int main(void) {
    for (unsigned b = 0; b < 2; b++) {
        check("not_ret", b, call_dirty((void *)_tcg_b1_not_ret, b));
        check("not_pass", b, call_dirty((void *)_tcg_b1_not_pass, b));
        check("not_zext", b, call_dirty((void *)_tcg_b1_not_zext, b));
    }
    printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
"#;

#[test]
fn negated_bools_cross_the_abi_as_clean_32_bit_bools_when_run() {
    let test = "negated_bools_cross_the_abi_as_clean_32_bit_bools_when_run";
    let names = [NOT_RET, NOT_PASS, NOT_ZEXT];
    let format = if HOST_IS_MACHO {
        X86OutputFormat::MachO
    } else {
        X86OutputFormat::Elf
    };
    let mut objects = Vec::new();
    for opt_level in OPT_LEVELS {
        let functions: Vec<X86ISelFunction> = lir_functions()
            .iter()
            .map(|(func, value_types)| select(func, value_types))
            .collect();
        let object = pipeline(opt_level, format)
            .compile_module(&functions)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error:?}"));
        assert_host_x86_64_object(test, &object, &names, &[SINK]);
        objects.push((opt_level, object));
    }
    if !x86_64_link_run_or_skip(test, "x86-64 link/run leg") {
        return;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("bool_not_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("bool_not_{opt_level:?}"));
        let mut link = x86_64_cc();
        link.arg("-o").arg(&binary).arg(&driver).arg(&object_path);
        let linked = command_output_with_timeout(&mut link, codegen_link_timeout()).unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        eprintln!("[{test}] {opt_level:?}:\n{stdout}");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt_level:?}: a negated bool crossed the ABI with bits above bit 0 set \
             (status {:?}):\n{stdout}",
            run.output.status
        );
        assert!(stdout.contains("failures=0"), "{opt_level:?}:\n{stdout}");
    }
    let _ = fs::remove_dir_all(&dir);
}

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

/// `f(p0: param) -> ret { %10 = node; return %10 }`.
fn trust_ir_module(param: Ty, ret: Ty, node: Inst) -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_bool_not_abi");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![param.clone()],
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(0), "_tcg_refused", ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), param)],
        body: vec![
            InstrNode::new(node).with_result(v(10)),
            InstrNode::new(Inst::Return {
                values: vec![v(10)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The AOT compile the trust-cg CLI makes (no trust-ir validation on its
/// path) refuses both shapes on x86-64 at O0 and O2 instead of emitting a
/// dirty `B1`.
#[test]
fn the_aot_compiler_refuses_scalar_bool_not_and_bitcast_into_bool() {
    let triple = if HOST_IS_MACHO {
        "x86_64-apple-darwin"
    } else {
        "x86_64-unknown-linux-gnu"
    };
    let spec = TargetSpec::parse(triple).unwrap();
    let rows = [
        (
            "not bool",
            trust_ir_module(
                Ty::Bool,
                Ty::Bool,
                Inst::UnOp {
                    op: UnOp::Not,
                    ty: Ty::Bool,
                    operand: v(0),
                },
            ),
            "UnOp::Not",
        ),
        (
            "bitcast u8 -> bool",
            trust_ir_module(
                Ty::U8,
                Ty::Bool,
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: Ty::U8,
                    dst_ty: Ty::Bool,
                    operand: v(0),
                },
            ),
            "Bitcast",
        ),
    ];
    for (name, module, needle) in rows {
        for opt_level in [
            trust_cg_codegen::pipeline::OptLevel::O0,
            trust_cg_codegen::pipeline::OptLevel::O2,
        ] {
            let result = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                spec,
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module);
            let error = match result {
                Ok(_) => panic!("{name} at {opt_level:?}: compiled; it must be refused"),
                Err(error) => error.to_string(),
            };
            // A row trust-ir itself refuses (`not` on a `bool` is
            // `BinOpRequiresInteger`) is refused at ingestion by that finding
            // since WS7.3; the others by the backend's own named refusal.
            match admission_expect::names_first_finding(&module, &error, &permit_unlicensed()) {
                Some(named) => assert!(
                    named,
                    "{name} at {opt_level:?}: trust-ir's finding {:?} not named: {error}",
                    admission_expect::first_finding(&module, &permit_unlicensed())
                ),
                None => assert!(
                    error.contains(needle) && error.contains("Bool"),
                    "{name} at {opt_level:?}: {error}"
                ),
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
