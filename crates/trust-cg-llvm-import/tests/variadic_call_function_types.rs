// Copyright 2026 Andrew Yates | Apache-2.0
//! A direct call's own function type decides its fixed/anonymous argument
//! split, and the importer either carries that split on the callee or refuses
//! the call by name.
//!
//! LLVM places a call's arguments by the function type the CALL states, not
//! by the callee's header. trust-ir carries one signature per callee, so:
//!
//! * an unprototyped `declare i32 @f(...)` (K&R `int f()`; clang calls it as
//!   `i32 (i32, i32, ...)` on x86-64 and as the non-variadic `i32 (i32, i32)`
//!   on AArch64) takes the type its calls state, when they all state one,
//!   in either declaration order;
//! * a call whose stated split differs from its callee's signature (review
//!   finding F5: `call i32 (i32, i32, ...) @f` against
//!   `declare i32 @f(i32, ...)` lowered with ONE fixed argument, so DarwinPCS
//!   got the second argument from the stack) is refused at import;
//! * a call that states `(...)` itself (C23 `int f(...)`) leaves the callee
//!   with no fixed prefix, which the backend cannot tell apart from a
//!   producer's unsigned placeholder: it is refused by
//!   `[TCG-UNSIGNED-VARIADIC]` (decision OD-55).

use trust_cg_llvm_import::import_text;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{AdapterError, GuardCarrierArch, TlsDialect};
use trust_ir::{FuncTy, Module, Ty};

const TARGETS: [(&str, GuardCarrierArch, TlsDialect); 3] = [
    (
        "x86_64-unknown-linux-gnu",
        GuardCarrierArch::X86_64,
        TlsDialect::ElfExecutable,
    ),
    (
        "aarch64-unknown-linux-gnu",
        GuardCarrierArch::AArch64,
        TlsDialect::ElfExecutable,
    ),
    (
        "aarch64-apple-darwin",
        GuardCarrierArch::AArch64,
        TlsDialect::MachOTlv,
    ),
];

fn target(triple: &str) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn import(name: &str, ir: &str) -> Module {
    import_text(ir, name).unwrap_or_else(|error| panic!("{name}: import failed: {error}"))
}

fn callee_signature<'m>(module: &'m Module, callee: &str) -> &'m FuncTy {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == callee)
        .unwrap_or_else(|| panic!("`@{callee}` imported"));
    module.func_type(function.ty).expect("registered signature")
}

/// Lower `module` for every target and return `caller`'s call opcode per
/// target, or the refusal.
fn lower_calls(module: &Module, caller: &str) -> Vec<(&'static str, Result<Opcode, AdapterError>)> {
    TARGETS
        .iter()
        .map(|&(triple, arch, dialect)| {
            let mut module = module.clone();
            module.target_info = Some(target(triple));
            let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &module,
                arch,
                dialect,
                &permit_unlicensed(),
            )
            .map(|functions| {
                let function = functions
                    .into_iter()
                    .map(|(function, _)| function)
                    .find(|function| function.name == caller)
                    .expect("caller lowered");
                let mut calls = function
                    .blocks
                    .values()
                    .flat_map(|block| &block.instructions)
                    .map(|instruction| instruction.opcode.clone())
                    .filter(|opcode| {
                        matches!(opcode, Opcode::Call { .. } | Opcode::CallVariadic { .. })
                    });
                let call = calls.next().expect("one call");
                assert!(calls.next().is_none(), "{triple}: exactly one call");
                call
            });
            (triple, lowered)
        })
        .collect()
}

fn assert_variadic_on_every_target(module: &Module, what: &str, fixed: u32) {
    for (triple, lowered) in lower_calls(module, "g") {
        let opcode = lowered.unwrap_or_else(|error| panic!("{what} {triple}: {error}"));
        assert!(
            matches!(&opcode, Opcode::CallVariadic { name, fixed_args } if name == "f" && *fixed_args == fixed),
            "{what} {triple}: expected CallVariadic {{ f, fixed_args: {fixed} }}, got {opcode:?}"
        );
    }
}

/// x86-64 K&R: clang calls `int f();` as `i32 (i32, i32, ...)`, every
/// argument fixed. The `(...)` declaration takes that type whether the
/// declaration comes before or after the call (clang writes it after).
#[test]
fn unprototyped_declaration_takes_the_variadic_type_its_calls_state() {
    let declare_first = "declare i32 @f(...)\n\
        define i32 @g(i32 %a) {\n\
        entry:\n  %r = call i32 (i32, i32, ...) @f(i32 %a, i32 7)\n  \
        %s = call i32 (i32, i32, ...) @f(i32 %r, i32 8)\n  ret i32 %s\n}\n";
    let clang_order = "define i32 @g(i32 %a) {\n\
        entry:\n  %r = call i32 (i32, i32, ...) @f(i32 %a, i32 7)\n  ret i32 %r\n}\n\
        declare i32 @f(...)\n";
    for (name, ir) in [
        ("declare_first", declare_first),
        ("clang_order", clang_order),
    ] {
        let module = import(name, ir);
        assert_eq!(
            callee_signature(&module, "f"),
            &FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: true,
            },
            "{name}"
        );
        if name == "clang_order" {
            assert_variadic_on_every_target(&module, name, 2);
        }
    }
}

/// AArch64 K&R: clang calls `int f();` as the non-variadic `i32 (i32, i32)`.
/// The declaration becomes that ordinary signature, in both orders.
#[test]
fn unprototyped_declaration_takes_the_non_variadic_type_its_calls_state() {
    let declare_first = "declare i32 @f(...)\n\
        define i32 @g(i32 %a) {\n\
        entry:\n  %r = call i32 @f(i32 %a, i32 7)\n  ret i32 %r\n}\n";
    let clang_order = "define i32 @g(i32 %a) {\n\
        entry:\n  %r = call i32 @f(i32 %a, i32 7)\n  ret i32 %r\n}\n\
        declare i32 @f(...)\n";
    for (name, ir) in [
        ("declare_first", declare_first),
        ("clang_order", clang_order),
    ] {
        let module = import(name, ir);
        assert_eq!(
            callee_signature(&module, "f"),
            &FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            },
            "{name}"
        );
        for (triple, lowered) in lower_calls(&module, "g") {
            let opcode = lowered.unwrap_or_else(|error| panic!("{name} {triple}: {error}"));
            assert!(
                matches!(&opcode, Opcode::Call { name, .. } if name == "f"),
                "{name} {triple}: {opcode:?}"
            );
        }
    }
}

/// Calls that state different types for one callee have no single
/// signature: the importer refuses the one that disagrees, by callee and
/// line. Covers the K&R arity mix clang accepts for `int f();`, and review
/// finding F5 (a call's split against a signed variadic declaration).
#[test]
fn a_call_whose_split_differs_from_its_callee_is_refused_at_import() {
    let cases = [
        (
            "knr_two_arities",
            "declare i32 @f(...)\n\
             define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 (i32, i32, ...) @f(i32 %a, i32 7)\n  \
             %s = call i32 (...) @f()\n  ret i32 %s\n}\n",
            "line 5",
        ),
        (
            "knr_c23_then_prototyped",
            "declare i32 @f(...)\n\
             define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 (...) @f(i32 %a)\n  \
             %s = call i32 @f(i32 %r, i32 7)\n  ret i32 %s\n}\n",
            "line 4",
        ),
        (
            "f5_signed_declaration_longer_call_prefix",
            "declare i32 @f(i32, ...)\n\
             define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 (i32, i32, ...) @f(i32 %a, i32 7)\n  ret i32 %r\n}\n",
            "line 4",
        ),
        (
            "f5_signed_declaration_non_variadic_call",
            "declare i32 @f(i32, ...)\n\
             define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 @f(i32 %a, i32 7)\n  ret i32 %r\n}\n",
            "line 4",
        ),
        (
            "f5_declare_by_use_then_other_prefix",
            "define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 (i32, ...) @f(i32 %a, i32 7)\n  \
             %s = call i32 (i32, i32, ...) @f(i32 %r, i32 7)\n  ret i32 %s\n}\n\
             declare i32 @f(i32, ...)\n",
            "line 4",
        ),
    ];
    for (name, ir, line) in cases {
        let error = import_text(ir, name)
            .map(|_| ())
            .expect_err(&format!("{name}: a disagreeing call must not import"));
        let message = error.to_string();
        assert!(
            message.contains("call to `@f`")
                && message.contains(line)
                && message.contains("fixed/anonymous argument split"),
            "{name}: {message}"
        );
    }
}

/// A call that states `(...)` itself leaves the callee without a fixed
/// prefix. The backend cannot tell it from the producer's unsigned
/// placeholder, so it refuses the call by name on every target (OD-55).
#[test]
fn a_zero_fixed_variadic_call_stays_refused_by_the_backend() {
    let cases = [
        (
            "c23_zero_fixed",
            "declare i32 @f(...)\n\
             define i32 @g(i32 %a) {\n\
             entry:\n  %r = call i32 (...) @f(i32 %a)\n  ret i32 %r\n}\n",
        ),
        (
            "zero_argument",
            "declare i32 @f(...)\n\
             define i32 @g() {\n\
             entry:\n  %r = call i32 (...) @f()\n  ret i32 %r\n}\n",
        ),
    ];
    for (name, ir) in cases {
        let module = import(name, ir);
        let signature = callee_signature(&module, "f");
        assert!(
            signature.is_vararg && signature.params.is_empty(),
            "{name}: {signature:?}"
        );
        for (triple, lowered) in lower_calls(&module, "g") {
            let error = lowered.expect_err(&format!("{name} {triple}: must not lower"));
            assert!(
                matches!(&error, AdapterError::UnsignedVariadicCallee { callee, .. } if callee == "f"),
                "{name} {triple}: {error:?}"
            );
        }
    }
}

/// Control: a call that states its callee's own split lowers with that
/// split, including when a parenthesized return attribute precedes the
/// call's function type.
#[test]
fn a_call_that_states_its_callees_split_lowers_with_it() {
    let printf = "declare i32 @f(ptr, ...)\n\
        define i32 @g(ptr %p, i32 %a) {\n\
        entry:\n  %r = call i32 (ptr, ...) @f(ptr %p, i32 %a)\n  ret i32 %r\n}\n";
    let module = import("printf_shape", printf);
    assert_variadic_on_every_target(&module, "printf_shape", 1);

    let attributed = "declare ptr @f(ptr, ...)\n\
        define ptr @g(ptr %p, i32 %a) {\n\
        entry:\n  %r = call noundef dereferenceable(8) ptr (ptr, ...) @f(ptr %p, i32 %a)\n  \
        ret ptr %r\n}\n";
    let module = import("attributed_return", attributed);
    assert_eq!(
        callee_signature(&module, "f"),
        &FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: true,
        }
    );
    assert_variadic_on_every_target(&module, "attributed_return", 1);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
