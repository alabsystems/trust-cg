// trust-cg-codegen - a select after a call re-tests its own condition
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A select whose condition is a `bool` loaded before a call must test that
//! bool after the call: AAPCS64 does not preserve NZCV across a call. The
//! callee here returns with Z set (`cmp xzr, xzr`), so a select that read the
//! callee's flags with `NE` would take its else arm for a true bool.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{CastOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "select_loaded_bool_after_call";
const THEN: u64 = 0x7e57;
const ELSE: u64 = 0xe15e;

/// Returns with Z and C set and N and V clear.
extern "C" fn return_with_z_set() {
    // SAFETY: compares the zero register with itself; no memory or stack.
    unsafe { core::arch::asm!("cmp xzr, xzr", options(nomem, nostack)) };
}

/// `fn(flag: *const bool, then: u64, else: u64, callee: u64) -> u64`:
/// load the bool, call `callee` indirectly, then select on the bool.
///
/// The callee address becomes a `ptr`: trust-ir's `IntToPtr` produces only
/// `Ty::Ptr` (an `inttoptr` to a `Ty::Func` is `CastIncompatible`, which every
/// ingestion entry refuses since WS7.3), and `CallIndirect` takes a
/// pointer-like callee at its declared signature.
fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_select_flags_across_call");
    let callee_ty = mb.add_func_type(vec![], vec![]);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let entry = fb.create_block();
    let flag_ptr = fb.add_block_param(entry, Ty::Ptr);
    let then_val = fb.add_block_param(entry, Ty::U64);
    let else_val = fb.add_block_param(entry, Ty::U64);
    let callee_raw = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let flag = fb.load(Ty::Bool, flag_ptr);
    let callee = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, callee_raw);
    fb.call_indirect_void(callee, callee_ty, vec![]);
    let chosen = fb.select(Ty::U64, flag, then_val, else_val);
    fb.ret(vec![chosen]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_select_on_a_bool_loaded_before_a_call_reads_the_bool_not_the_callees_flags() {
    let module = build_module();
    let callee = return_with_z_set as *const () as usize as u64;
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) -> u64,
        // and `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> u64>(ENTRY)
        }
        .expect("entry symbol");
        for (byte, expected) in [(1u8, THEN), (0u8, ELSE)] {
            assert_eq!(
                entry.as_ref()(&byte, THEN, ELSE, callee),
                expected,
                "{opt_level:?}: bool byte {byte}"
            );
        }
    }
}

/// This file's fixture is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
