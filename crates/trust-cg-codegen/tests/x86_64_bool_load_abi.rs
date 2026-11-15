// trust-cg-codegen/tests/x86_64_bool_load_abi.rs - a loaded `bool` is a clean 32-bit bool at the ABI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A `bool` the x86-64 backend defines by a LOAD is the backend's clean 32-bit
//! boolean wherever it crosses the ABI: returned in EAX, and passed as a call
//! argument at 32 bits, which an LLVM callee of a `bool` argument relies on
//! (`fn(b: bool) -> u32 { b as u32 }` is `movl %edi, %eax`).
//!
//! `mov r8, m` writes only the low byte of its destination, and register
//! allocation treats that destination as a pure definition, so bits 8..31 are
//! whatever the assigned register held. Measured before the fix through the
//! rustc bridge: `movb (%rax), %cl; movl %ecx, %eax` returned `0x123456xx`
//! with the caller's RCX preloaded. And the loaded byte `m` is trust-ir's bool
//! `m != 0` (the reference interpreter's `Load Bool`), whatever `m` is. The
//! selector computes it for every `B1` load (plain, volatile, atomic):
//! `movzx z, r8; add t, z, 255; shr b, t, 8`. A stack-passed `bool`
//! parameter, a value whose byte the caller's convention makes 0 or 1, is
//! zero-extended.
//!
//! Two legs, each at O0 and O2 through `X86Pipeline`:
//!
//! * host-neutral: after the production x86 pass order, the register moved
//!   into EAX before `RET` and into EDI before `CALL` is that `!= 0` of the
//!   `MOVZX` of the loaded register (for the stack parameter, the `MOVZX`),
//!   so no pass deleted the normalization;
//! * native (an x86-64 host that links and runs x86-64): the emitted object is
//!   linked against a C driver whose trampoline fills every general-purpose
//!   register (and the stack bool's slot above its byte) with `0xA5` bytes
//!   before the call; with each loaded byte 0, 1, 2, 0x80 and 0xFF, the
//!   returned EAX and the callee's EDI must be exactly `byte != 0`.

mod common;

use std::fs;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};
use common::x86_64_object::{HOST_IS_MACHO, assert_host_x86_64_object};
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{EAX, EDI, X86PReg};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{
    X86ISelFunction, X86ISelInst, X86ISelOperand, X86InstructionSelector,
};
use trust_cg_opt::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Linkage, Module as TrustIrModule, Ordering, Ty, ValueId,
};

const OPT_LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// The C callee: returns its whole 32-bit argument register.
const SINK: &str = "_bool_sink";
const LOAD: &str = "_tcg_load_bool";
const LOAD_VOLATILE: &str = "_tcg_load_bool_volatile";
const LOAD_ATOMIC: &str = "_tcg_load_bool_atomic";
const PASS: &str = "_tcg_pass_loaded_bool";
const PASS_STACK: &str = "_tcg_pass_stack_bool";

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn add_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn load_bool(volatile: bool) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty: Ty::Bool,
        ptr: v(0),
        volatile,
        align: None,
    })
    .with_result(v(10))
}

fn ret(value: ValueId) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![value],
    })
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_bool_load_abi");
    let sink_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut external = TrustIrFunction::new(FuncId::new(0), SINK, sink_ty, BlockId::new(0));
    external.blocks.clear();
    external.linkage = Linkage::External;
    let sink = external.id;
    module
        .try_add_function(external)
        .expect("Module::try_add_function: test fixture");
    add_function(
        &mut module,
        1,
        LOAD,
        vec![Ty::Ptr],
        vec![Ty::Bool],
        vec![load_bool(false), ret(v(10))],
    );
    add_function(
        &mut module,
        2,
        LOAD_VOLATILE,
        vec![Ty::Ptr],
        vec![Ty::Bool],
        vec![load_bool(true), ret(v(10))],
    );
    add_function(
        &mut module,
        3,
        LOAD_ATOMIC,
        vec![Ty::Ptr],
        vec![Ty::Bool],
        vec![
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::Bool,
                ptr: v(0),
                ordering: Ordering::Acquire,
            })
            .with_result(v(10)),
            ret(v(10)),
        ],
    );
    add_function(
        &mut module,
        4,
        PASS,
        vec![Ty::Ptr],
        vec![Ty::I32],
        vec![
            load_bool(false),
            InstrNode::new(Inst::Call {
                callee: sink,
                args: vec![v(10)],
            })
            .with_result(v(11)),
            ret(v(11)),
        ],
    );
    // Six integer registers, then the `bool` on the stack.
    let mut stack_params = vec![Ty::I64; 6];
    stack_params.push(Ty::Bool);
    add_function(
        &mut module,
        5,
        PASS_STACK,
        stack_params,
        vec![Ty::I32],
        vec![
            InstrNode::new(Inst::Call {
                callee: sink,
                args: vec![v(6)],
            })
            .with_result(v(11)),
            ret(v(11)),
        ],
    );
    module
}

/// The real adapter and the real x86-64 instruction selector.
fn select(module: &TrustIrModule, name: &str) -> X86ISelFunction {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function {name}"));
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
            .unwrap_or_else(|error| panic!("{name}: the adapter must lower it: {error:?}"));
    let mut isel = X86InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    isel.set_stack_slots(lir.stack_slots.clone());
    isel.seed_value_types(&lir.value_types);
    isel.seed_function_value_use_counts(&lir);
    isel.lower_formal_arguments(&lir.signature, lir.entry_block)
        .unwrap_or_else(|error| panic!("{name}: formal arguments: {error:?}"));
    for block in lir.layout_order() {
        isel.select_block(block, &lir.blocks[&block].instructions)
            .unwrap_or_else(|error| panic!("{name}: selection: {error:?}"));
    }
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

/// The row defining the register `reg` read at `before`, following register
/// copies back: `(row, the register it defines)`.
fn defining_row(insts: &[X86ISelInst], before: usize, reg: VReg) -> Option<usize> {
    let (mut at, mut cur) = (before, reg);
    loop {
        let def = definition(insts, at, cur)?;
        match (insts[def].opcode, insts[def].operands.as_slice()) {
            (X86Opcode::MovRR | X86Opcode::MovRR32, [_, X86ISelOperand::VReg(src)]) => {
                (at, cur) = (def, *src);
            }
            _ => return Some(def),
        }
    }
}

/// Whether the register `reg` read at `before` is a zero-extended byte load,
/// following register copies back: the zero-extending load itself (`movzx
/// r32, m8`, the selector's byte load), or a `MOVZX` of a byte-load
/// destination.
fn is_zero_extended_byte_load(insts: &[X86ISelInst], before: usize, reg: VReg) -> bool {
    let Some(def) = defining_row(insts, before, reg) else {
        return false;
    };
    let byte_load = |opcode| {
        matches!(
            opcode,
            X86Opcode::MovRM8
                | X86Opcode::VolatileMovRM8
                | X86Opcode::MovRM8Sib
                | X86Opcode::MovzxRM8
                | X86Opcode::VolatileMovzxRM8
                | X86Opcode::MovzxRM8Sib
        )
    };
    match (insts[def].opcode, insts[def].operands.as_slice()) {
        (X86Opcode::MovzxRM8 | X86Opcode::VolatileMovzxRM8 | X86Opcode::MovzxRM8Sib, [_, _]) => {
            true
        }
        (X86Opcode::Movzx, [_, X86ISelOperand::VReg(src)]) => {
            definition(insts, def, *src).is_some_and(|load| byte_load(insts[load].opcode))
        }
        _ => false,
    }
}

/// Whether the register `reg` read at `before` is the `!= 0` test of a
/// loaded byte, following register copies back: `shr b, t, 8` of `add t, z,
/// 255` of the `MOVZX` of a byte-load destination (`b = (m + 255) >> 8`).
fn is_nonzero_test_of_byte_load(insts: &[X86ISelInst], before: usize, reg: VReg) -> bool {
    let Some(shr) = defining_row(insts, before, reg) else {
        return false;
    };
    let [_, X86ISelOperand::VReg(biased), X86ISelOperand::Imm(8)] = insts[shr].operands.as_slice()
    else {
        return false;
    };
    if insts[shr].opcode != X86Opcode::ShrRI {
        return false;
    }
    let Some(add) = defining_row(insts, shr, *biased) else {
        return false;
    };
    match (insts[add].opcode, insts[add].operands.as_slice()) {
        (X86Opcode::AddRI, [_, X86ISelOperand::VReg(byte), X86ISelOperand::Imm(0xFF)]) => {
            is_zero_extended_byte_load(insts, add, *byte)
        }
        _ => false,
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
fn loaded_bools_are_zero_extended_before_every_abi_boundary_after_the_x86_passes() {
    let module = build_module();
    for opt_level in OPT_LEVELS {
        for (name, preg, boundary) in [
            (LOAD, EAX, X86Opcode::Ret),
            (LOAD_VOLATILE, EAX, X86Opcode::Ret),
            (LOAD_ATOMIC, EAX, X86Opcode::Ret),
            (PASS, EDI, X86Opcode::Call),
        ] {
            let mut func = select(&module, name);
            let _ = pipeline(opt_level, X86OutputFormat::RawBytes)
                .run_x86_optimization_passes(&mut func);
            let insts = entry(&func);
            let (copy, src) = copied_into_before(insts, preg, boundary);
            assert!(
                is_nonzero_test_of_byte_load(insts, copy, src),
                "{name} at {opt_level:?}: the bool reaching {preg:?} before {boundary:?} is \
                 not the `!= 0` test of a zero-extended byte load: {insts:#?}"
            );
        }
        // The stack-passed `bool` parameter: `movzx r32, byte [rbp + 16]`.
        let mut func = select(&module, PASS_STACK);
        let _ =
            pipeline(opt_level, X86OutputFormat::RawBytes).run_x86_optimization_passes(&mut func);
        let insts = entry(&func);
        let (copy, src) = copied_into_before(insts, EDI, X86Opcode::Call);
        assert!(
            is_zero_extended_byte_load(insts, copy, src),
            "{PASS_STACK} at {opt_level:?}: the stack bool reaching EDI is not zero-extended: \
             {insts:#?}"
        );
    }
}

/// The driver's trampolines fill every general-purpose register other than
/// RSP/RBP (and the stack bool's slot above its byte) with `0xA5` bytes, call,
/// and hand back RAX whole. System V: entry RSP is 8 mod 16; the six pushes
/// and one more 8-byte slot align it for the call.
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

/* uint64_t call_dirty(void *fn, uint64_t arg): fn(arg) */
__asm__(
    ".text\n"
    ".globl " SYM(call_dirty) "\n"
    SYM(call_dirty) ":\n"
    "  pushq %rbp\n  movq %rsp, %rbp\n"
    "  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
    "  subq $8, %rsp\n"
    "  movq %rdi, %r11\n  movq %rsi, %rdi\n"
    "  movabsq " DIRTY ", %rsi\n"
    FILL_SCRATCH
    "  callq *%r11\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n"
    "  popq %rbp\n  retq\n");

/* uint64_t call_dirty_stack(void *fn, uint64_t b): fn(D, D, D, D, D, D, b) with
   the bytes of b's stack slot above its low byte dirty too */
__asm__(
    ".text\n"
    ".globl " SYM(call_dirty_stack) "\n"
    SYM(call_dirty_stack) ":\n"
    "  pushq %rbp\n  movq %rsp, %rbp\n"
    "  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
    "  movq %rdi, %r11\n"
    "  movabsq $0xa5a5a5a5a5a5a500, %rax\n  orq %rsi, %rax\n  pushq %rax\n"
    "  movabsq " DIRTY ", %rdi\n  movq %rdi, %rsi\n"
    FILL_SCRATCH
    "  callq *%r11\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n"
    "  popq %rbp\n  retq\n");

uint64_t call_dirty(void *fn, uint64_t arg);
uint64_t call_dirty_stack(void *fn, uint64_t b);

extern unsigned char _tcg_load_bool(const unsigned char *);
extern unsigned char _tcg_load_bool_volatile(const unsigned char *);
extern unsigned char _tcg_load_bool_atomic(const unsigned char *);
extern unsigned _tcg_pass_loaded_bool(const unsigned char *);
extern unsigned _tcg_pass_stack_bool(long, long, long, long, long, long, unsigned char);

/* The callee reads its whole 32-bit argument register, as an LLVM callee of a
   `bool` argument does. */
unsigned _bool_sink(unsigned b) { return b; }

static int failures = 0;

/* A loaded bool is its byte read as `!= 0` (trust-ir's `Load Bool`), in all
   32 bits of the register it crosses the ABI in. */
static void check(const char *what, unsigned byte, unsigned want, uint64_t rax) {
    uint32_t eax = (uint32_t)rax;
    printf("%s(0x%02x) eax=0x%08x\n", what, byte, eax);
    if (eax != want) failures++;
}

static const unsigned char BYTES[] = {0, 1, 2, 0x80, 0xFF};

int main(void) {
    for (unsigned i = 0; i < sizeof BYTES; i++) {
        unsigned char byte = BYTES[i];
        unsigned b = byte != 0;
        check("load", byte, b, call_dirty((void *)_tcg_load_bool, (uint64_t)(uintptr_t)&byte));
        check("load_volatile", byte, b,
              call_dirty((void *)_tcg_load_bool_volatile, (uint64_t)(uintptr_t)&byte));
        check("load_atomic", byte, b,
              call_dirty((void *)_tcg_load_bool_atomic, (uint64_t)(uintptr_t)&byte));
        check("pass", byte, b,
              call_dirty((void *)_tcg_pass_loaded_bool, (uint64_t)(uintptr_t)&byte));
    }
    /* A stack-passed `bool` parameter is a value the caller's convention
       makes 0 or 1 (psABI), not a trust-ir `Load`. */
    for (unsigned b = 0; b < 2; b++) {
        check("pass_stack", b, b, call_dirty_stack((void *)_tcg_pass_stack_bool, b));
    }
    printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
"#;

#[test]
fn loaded_bools_cross_the_abi_as_clean_32_bit_bools_when_run() {
    let test = "loaded_bools_cross_the_abi_as_clean_32_bit_bools_when_run";
    let module = build_module();
    let names = [LOAD, LOAD_VOLATILE, LOAD_ATOMIC, PASS, PASS_STACK];
    let format = if HOST_IS_MACHO {
        X86OutputFormat::MachO
    } else {
        X86OutputFormat::Elf
    };
    let mut objects = Vec::new();
    for opt_level in OPT_LEVELS {
        let functions: Vec<X86ISelFunction> =
            names.iter().map(|name| select(&module, name)).collect();
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
        let object_path = dir.join(format!("bool_load_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("bool_load_{opt_level:?}"));
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
            "{opt_level:?}: a loaded bool crossed the ABI as something other than `byte != 0` \
             (status {:?}):\n{stdout}",
            run.output.status
        );
        assert!(stdout.contains("failures=0"), "{opt_level:?}:\n{stdout}");
    }
    let _ = fs::remove_dir_all(&dir);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
