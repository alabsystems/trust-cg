// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A `u32` switch dispatched through a jump table, run natively with a
//! caller that leaves bits above 31 set in the selector's register: a `u32`
//! argument with RDI's high half set (the psABI does not define those bits
//! of a 32-bit argument), and `match x as u32` on a `u64` argument whose
//! high half is set (the truncation may leave it in the register).
//!
//! In the instruction-selection stream a `Gpr32` virtual register's bits
//! above 31 are undefined, so the selector's former copy of a 32-bit
//! selector into the 64-bit bound check and table index, a 64-bit `mov`, is
//! refuted by the x86-64 source-bound body theorem (slice 14, OD-181); the
//! selector now copies it with the zero-extending 32-bit `mov`. That is a
//! hardening of the pre-RA stream, not the fix of an observed miscompile:
//! natively, the former form returned the right value in both contexts
//! measured here (downstream stages leave the bits clear). These tests
//! compile the selector's stream as it is and, rebuilt, in the former form,
//! link each with a C driver that calls through inline assembly, assert the
//! current form against the source's `match`, and print what the former
//! form returns (`S14_FORMER_U32_DISPATCH`, `TRUNC_FORMER_U32_DISPATCH`).

mod common;
use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};

use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::RegClass;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::Function;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelFunction, X86ISelOperand, X86InstructionSelector,
};
use trust_ir::{Constant, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const NAME: &str = "s14_table_u32";

/// `fn s14_table_u32(x: u32) -> u64 { match x { 0 => 10, 1 => 11, 2 => 12,
/// 3 => 13, _ => 99 } }`, through the trust-ir adapter.
fn lir() -> Function {
    lir_with(false)
}

/// `truncate`: the parameter is a `u64` and the switch is on `x as u32`, so
/// the selector's register may hold the parameter's defined high half.
fn lir_with(truncate: bool) -> Function {
    let mut builder = ModuleBuilder::new("e2e_x86_64_jump_table_selector_width");
    let param = if truncate { Ty::U64 } else { Ty::U32 };
    let signature = builder.add_func_type(vec![param.clone()], vec![Ty::U64]);
    let mut f = builder.function(NAME, signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, param);
    f.switch_to_block(entry);
    let x = if truncate {
        f.trunc(Ty::U64, Ty::U32, x)
    } else {
        x
    };
    let arms: Vec<_> = (0..5).map(|_| f.create_block()).collect();
    f.switch(
        x,
        (0..4)
            .map(|k| SwitchCase {
                value: Constant::Int(k as i128),
                target: arms[k],
                args: vec![],
            })
            .collect(),
        arms[4],
        vec![],
    );
    for (k, arm) in arms.iter().enumerate() {
        f.switch_to_block(*arm);
        let value = f.iconst(Ty::U64, if k < 4 { 10 + k as i128 } else { 99 });
        f.ret(vec![value]);
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("translates")
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == NAME)
    .expect("translated")
}

/// The AOT selection sequence (as the verify crate's fixtures run it).
fn select(source: &Function) -> X86ISelFunction {
    let signature = trust_cg_lower::function::Signature {
        params: source.signature.params.clone(),
        returns: source.signature.returns.clone(),
    };
    let mut isel = X86InstructionSelector::with_abi(
        source.name.clone(),
        signature.clone(),
        X86CallAbi::SystemV,
    );
    isel.set_stack_slots(source.stack_slots.clone());
    isel.seed_value_types(&source.value_types);
    isel.seed_function_value_use_counts(source);
    isel.seed_pure_callees(&source.pure_callees);
    isel.seed_sret_param(source.abi_sret_param).unwrap();
    isel.seed_sret_arg_callees(&source.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&source.sret_arg_indirect_callees);
    let order = source.layout_order();
    isel.seed_iconst_origins(
        order
            .iter()
            .map(|block| source.blocks[block].instructions.as_slice()),
    );
    for block in &order {
        isel.ensure_block(*block);
    }
    isel.lower_formal_arguments(&signature, source.entry_block)
        .unwrap();
    for block in &order {
        let body = &source.blocks[block];
        if *block != source.entry_block && !body.params.is_empty() {
            isel.define_block_params(&body.params);
        }
        isel.select_block(*block, &body.instructions).unwrap();
    }
    isel.finalize_with_eh_info(&source.eh_info).unwrap()
}

/// The selector's 32-bit copy of the selector into the 64-bit index.
fn index_copy(machine: &X86ISelFunction) -> Option<(trust_cg_lower::instructions::Block, usize)> {
    machine.block_order.iter().find_map(|block| {
        machine.blocks[block]
            .insts
            .iter()
            .position(|inst| {
                inst.opcode == X86Opcode::MovRR32
                    && matches!(
                        inst.operands.as_slice(),
                        [X86ISelOperand::VReg(norm), X86ISelOperand::VReg(selector)]
                            if norm.class == RegClass::Gpr64 && selector.class == RegClass::Gpr32
                    )
            })
            .map(|index| (*block, index))
    })
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t SYMBOL(uint32_t);
static uint64_t call(uint64_t rdi) {
    uint64_t result;
    __asm__ volatile(
        "mov %1, %%rdi\n\t"
        "call " CALLEE "\n\t"
        "mov %%rax, %0"
        : "=r"(result)
        : "r"(rdi)
        : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "memory", "cc");
    return result;
}
int main(void) {
    for (uint64_t k = 0; k < 6; k++) {
        printf("%llu %llu\n", (unsigned long long)call(k),
               (unsigned long long)call(k | 0xdead000000000000ull));
    }
    return 0;
}
"#;

/// Compile, link with the driver and run; the driver prints, for x = 0..5,
/// the result with a clean RDI and with RDI's high bits set.
fn run(label: &str, machine: &X86ISelFunction) -> Option<Vec<(u64, u64)>> {
    let format = if cfg!(target_os = "macos") {
        X86OutputFormat::MachO
    } else {
        X86OutputFormat::Elf
    };
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: format,
        emit_frame: true,
        ..X86PipelineConfig::default()
    });
    let object = pipeline.compile_function(machine).expect("compiles");
    if !x86_64_link_run_or_skip(label, "x86-64 link/run leg") {
        return None;
    }
    let dir = std::env::temp_dir().join(format!("tcg_s14_table_{label}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let object_path = dir.join("subject.o");
    std::fs::write(&object_path, &object).unwrap();
    let symbol = if cfg!(target_os = "macos") {
        format!("_{NAME}")
    } else {
        NAME.to_owned()
    };
    let driver = DRIVER
        .replace("SYMBOL", NAME)
        .replace("CALLEE", &format!("\"{symbol}\""));
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).unwrap();
    let binary = dir.join("run");
    let mut link = x86_64_cc();
    // The driver calls from inline assembly: no red zone for it to clobber.
    link.args([
        "-mno-red-zone",
        "-o",
        binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        object_path.to_str().unwrap(),
    ]);
    let linked = command_output_with_timeout(&mut link, codegen_link_timeout()).expect("cc runs");
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{label}: link failed: {}",
        String::from_utf8_lossy(&linked.output.stderr)
    );
    let ran = run_executable_with_timeout(&binary, codegen_run_timeout()).expect("runs");
    assert!(
        !ran.timed_out && ran.output.status.success(),
        "{label}: run failed"
    );
    let _ = std::fs::remove_dir_all(&dir);
    Some(
        String::from_utf8_lossy(&ran.output.stdout)
            .lines()
            .map(|line| {
                let mut fields = line.split_whitespace().map(|f| f.parse::<u64>().unwrap());
                (fields.next().unwrap(), fields.next().unwrap())
            })
            .collect(),
    )
}

#[test]
fn a_u32_jump_table_dispatches_on_the_selectors_own_bits() {
    let source = lir();
    let current = select(&source);
    assert_eq!(current.jump_tables.len(), 1, "a jump table");
    let (block, index) = index_copy(&current).expect("the 32-bit index copy");
    let mut former = current.clone();
    former.blocks.get_mut(&block).unwrap().insts[index].opcode = X86Opcode::MovRR;
    let expected: Vec<u64> = vec![10, 11, 12, 13, 99, 99];
    let Some(results) = run("current", &current) else {
        return;
    };
    for (k, (clean, stray)) in results.iter().enumerate() {
        assert_eq!(*clean, expected[k], "x = {k}");
        assert_eq!(*stray, expected[k], "x = {k} with RDI's high bits set");
    }
    if let Some(results) = run("former", &former) {
        let wrong: Vec<_> = results
            .iter()
            .enumerate()
            .filter(|(k, (_, stray))| *stray != expected[*k])
            .map(|(k, (_, stray))| (k, *stray))
            .collect();
        eprintln!(
            "S14_FORMER_U32_DISPATCH wrong_with_stray_bits={wrong:?} (x, returned) of {} cases",
            results.len()
        );
    }
}

/// `match x as u32` on a `u64` argument whose high half is set: the selector's
/// value is the low 32 bits, and its register may still hold the high half
/// the truncation discarded.
#[test]
fn a_truncated_u32_jump_table_dispatches_on_the_low_32_bits() {
    let source = lir_with(true);
    let current = select(&source);
    assert_eq!(current.jump_tables.len(), 1, "a jump table");
    let expected: Vec<u64> = vec![10, 11, 12, 13, 99, 99];
    let former = index_copy(&current).map(|(block, index)| {
        let mut former = current.clone();
        former.blocks.get_mut(&block).unwrap().insts[index].opcode = X86Opcode::MovRR;
        former
    });
    let Some(results) = run("trunc_current", &current) else {
        return;
    };
    for (k, (clean, stray)) in results.iter().enumerate() {
        assert_eq!(*clean, expected[k], "x = {k}");
        assert_eq!(*stray, expected[k], "x = {k} with the u64's high bits set");
    }
    if let Some(former) = former
        && let Some(results) = run("trunc_former", &former)
    {
        let wrong: Vec<_> = results
            .iter()
            .enumerate()
            .filter(|(k, (_, stray))| *stray != expected[*k])
            .map(|(k, (_, stray))| (k, *stray))
            .collect();
        eprintln!(
            "TRUNC_FORMER_U32_DISPATCH wrong_with_high_bits={wrong:?} (x, returned) of {} cases",
            results.len()
        );
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
