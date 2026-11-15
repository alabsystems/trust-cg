// trust-cg-lower/tests/named_call_prototype.rs - a direct call is lowered by
// its callee's name only with the declared prototype that name needs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The adapter's `Inst::Call` lowering of the L02-P15 LD-74 re-check's
//! reproducers (LD-100 in `docs/decision-record.md`).
//! Before the ruling the adapter read a call of `memcpy`, `memmove` or
//! `memset` by the callee's NAME alone: `n1_memcpy_ints`
//! (`declare i64 @memcpy(i64, i64, i64)`) became `Opcode::Memcpy` copying 8
//! bytes from address 4 to address 3, and `n2_memset_ret_count` (`memset`
//! returning its count) defined its result as the destination address. Now a
//! declaration other than C's prototype and convention is an ordinary call of
//! the symbol, C's prototypes keep the bulk-memory operation, and an LLVM
//! intrinsic name declared at another type is refused by name.
//!
//! Public API only, so the file runs against an adapter without the rule.
//! The classification rules one by one are the unit tests of
//! `src/adapter_named_call_prototype_tests.rs`.

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, TlsDialect, UnlicensedBodyPolicy,
    translate_module_for_arch_with_tls_with_license,
};
use trust_ir::{CallingConv, Module, Ty};
use trust_ir_build::ModuleBuilder;

fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// `caller(...)` calling `callee_name`, declared `(params) -> (returns)`:
/// argument `i` is the constant `constants` gives for `i`, or else the
/// caller's own next parameter of that type; the caller returns the call's
/// result.
fn caller_module(
    callee_name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    constants: &[(usize, i128)],
) -> Module {
    let mut mb = ModuleBuilder::new("named_call_prototype");
    let callee_ty = mb.add_func_type(params.clone(), returns.clone());
    let callee = mb.declare_function(callee_name, callee_ty);
    let caller_params: Vec<Ty> = params
        .iter()
        .enumerate()
        .filter(|(index, _)| !constants.iter().any(|(at, _)| at == index))
        .map(|(_, ty)| ty.clone())
        .collect();
    let caller_ty = mb.add_func_type(caller_params, returns.clone());
    let mut f = mb.function("caller", caller_ty);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let mut args = Vec::with_capacity(params.len());
    for (index, ty) in params.iter().enumerate() {
        match constants.iter().find(|(at, _)| *at == index) {
            Some((_, value)) => args.push(f.iconst(ty.clone(), *value)),
            None => args.push(f.add_block_param(entry, ty.clone())),
        }
    }
    if returns.is_empty() {
        f.call_void(callee, args);
        f.ret(vec![]);
    } else {
        let result = f.call(callee, args);
        f.ret(vec![result]);
    }
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn lower(module: &Module) -> Result<Vec<Opcode>, String> {
    let lowered = translate_module_for_arch_with_tls_with_license(
        module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .map_err(|error| error.to_string())?;
    let (caller, _) = lowered
        .iter()
        .find(|(function, _)| function.name == "caller")
        .expect("the caller is lowered");
    Ok(caller
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter().map(|inst| inst.opcode.clone()))
        .collect())
}

fn caller_opcodes(module: &Module) -> Vec<Opcode> {
    lower(module).unwrap_or_else(|error| panic!("the module lowers: {error}"))
}

fn calls_symbol(opcodes: &[Opcode], symbol: &str) -> bool {
    opcodes
        .iter()
        .any(|opcode| matches!(opcode, Opcode::Call { name, .. } if name == symbol))
}

fn is_bulk_memory(opcode: &Opcode) -> bool {
    matches!(opcode, Opcode::Memcpy | Opcode::Memmove | Opcode::Memset)
}

/// Each declaration other than C's is called as the ordinary function it is.
#[test]
fn a_memory_routine_declared_otherwise_is_an_ordinary_call() {
    let cases: Vec<(&str, Module)> = vec![
        // n1_memcpy_ints: `declare i64 @memcpy(i64, i64, i64)`.
        (
            "memcpy",
            caller_module(
                "memcpy",
                vec![Ty::I64, Ty::I64, Ty::I64],
                vec![Ty::I64],
                &[(0, 3), (1, 4), (2, 8)],
            ),
        ),
        // n2_memset_ret_count: `declare i64 @memset(ptr, i32, i64)`.
        (
            "memset",
            caller_module(
                "memset",
                vec![Ty::Ptr, Ty::I32, Ty::I64],
                vec![Ty::I64],
                &[(1, 65), (2, 8)],
            ),
        ),
        // n3_memmove_ret_i32: `declare i32 @memmove(ptr, ptr, i64)`.
        (
            "memmove",
            caller_module(
                "memmove",
                vec![Ty::Ptr, Ty::Ptr, Ty::I64],
                vec![Ty::I32],
                &[],
            ),
        ),
        // `declare void @memcpy(ptr, ptr, i64)`.
        (
            "memcpy",
            caller_module("memcpy", vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![], &[(2, 8)]),
        ),
        // A 32-bit count.
        (
            "memcpy",
            caller_module(
                "memcpy",
                vec![Ty::Ptr, Ty::Ptr, Ty::I32],
                vec![Ty::Ptr],
                &[(2, 8)],
            ),
        ),
        // An 8-bit fill.
        (
            "memset",
            caller_module(
                "memset",
                vec![Ty::Ptr, Ty::I8, Ty::I64],
                vec![Ty::Ptr],
                &[(1, 65), (2, 8)],
            ),
        ),
    ];
    for (symbol, module) in &cases {
        let opcodes = caller_opcodes(module);
        assert!(calls_symbol(&opcodes, symbol), "{symbol}: {opcodes:?}");
        assert!(!opcodes.iter().any(is_bulk_memory), "{symbol}: {opcodes:?}");
    }
    // C's types under another convention.
    let mut fast_copy = caller_module(
        "memmove",
        vec![Ty::Ptr, Ty::Ptr, Ty::I64],
        vec![Ty::Ptr],
        &[(2, 8)],
    );
    fast_copy.functions[0].calling_conv = CallingConv::Fast;
    let opcodes = caller_opcodes(&fast_copy);
    assert!(calls_symbol(&opcodes, "memmove"), "{opcodes:?}");
    assert!(!opcodes.iter().any(is_bulk_memory), "{opcodes:?}");
}

/// Controls: C's prototypes, and LLVM's intrinsics at their own type, are
/// the bulk-memory operations, with no call of the name.
#[test]
fn c_prototypes_and_llvm_intrinsics_keep_the_bulk_memory_operation() {
    for (name, second, returns, opcode) in [
        ("memcpy", Ty::Ptr, vec![Ty::Ptr], Opcode::Memcpy),
        ("memmove", Ty::Ptr, vec![Ty::Ptr], Opcode::Memmove),
        ("memset", Ty::I32, vec![Ty::Ptr], Opcode::Memset),
        ("llvm.memcpy.p0.p0.i64", Ty::Ptr, vec![], Opcode::Memcpy),
        ("llvm.memset.p0.i64", Ty::I8, vec![], Opcode::Memset),
    ] {
        let module = caller_module(name, vec![Ty::Ptr, second, Ty::I64], returns, &[(2, 8)]);
        let opcodes = caller_opcodes(&module);
        assert!(opcodes.contains(&opcode), "{name}: {opcodes:?}");
        assert!(!calls_symbol(&opcodes, name), "{name}: {opcodes:?}");
    }
}

/// An LLVM intrinsic name declared at another type than its own fails the
/// module by name: an ordinary call would name a symbol no library defines.
#[test]
fn an_llvm_intrinsic_name_at_another_type_is_refused_by_name() {
    for (name, params, returns) in [
        (
            "llvm.memcpy.p0.p0.i64",
            vec![Ty::Ptr, Ty::Ptr, Ty::I64],
            vec![Ty::Ptr],
        ),
        (
            "llvm.memset.p0.i64",
            vec![Ty::Ptr, Ty::I32, Ty::I64],
            vec![],
        ),
        ("llvm.bitreverse.i32", vec![Ty::I64], vec![Ty::I64]),
    ] {
        let constants: Vec<(usize, i128)> = params
            .iter()
            .enumerate()
            .filter(|(_, ty)| !matches!(ty, Ty::Ptr))
            .map(|(index, _)| (index, 8))
            .collect();
        let module = caller_module(name, params, returns, &constants);
        let error = lower(&module).expect_err(name);
        assert!(
            error.contains("[TCG-NAMED-CALL-PROTOTYPE]") && error.contains(name),
            "{name}: {error}"
        );
    }
}
