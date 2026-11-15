// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The CLI surfaces the shared signature-level ABI refusals by name: a
//! variadic function definition (`[TCG-VARIADIC-DEFINITION]`) and a `byval`
//! parameter (`[TCG-BYVAL-ABI]`) fail compilation on the native and wasm
//! routes without writing an object, while a variadic CALL still compiles.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_cg_codegen::wasm;
use trust_ir::{Module, ParamAttrs, Ty};
use trust_ir_build::ModuleBuilder;

fn run(directory: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .arg("--permit-unlicensed")
        .current_dir(directory)
        .args(args)
        .output()
        .expect("run trust-cg")
}

/// `i64 first(i64 x, ...) { return x; }`.
fn variadic_definition() -> Module {
    let mut builder = ModuleBuilder::new("cli_variadic_definition");
    let signature = builder.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut function = builder.function("first", signature);
    let entry = function.create_block();
    let x = function.add_block_param(entry, Ty::I64);
    function.switch_to_block(entry);
    function.ret(vec![x]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// `i32 first(ptr p)` whose parameter carries `byval`.
fn byval_definition(result: Ty) -> Module {
    let mut builder = ModuleBuilder::new("cli_byval_definition");
    let signature = builder.add_func_type(vec![Ty::Ptr], vec![result.clone()]);
    let mut function = builder.function("first", signature);
    let entry = function.create_block();
    function.add_block_param(entry, Ty::Ptr);
    function.switch_to_block(entry);
    let zero = function.iconst(result, 0);
    function.ret(vec![zero]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].attrs.params = vec![ParamAttrs {
        byval: true,
        ..ParamAttrs::default()
    }];
    module
}

/// `i64 caller(i64 x) { return printf_like(x, x); }` with `printf_like` a
/// bodyless variadic declaration.
fn variadic_call() -> Module {
    let mut builder = ModuleBuilder::new("cli_variadic_call");
    let callee_signature = builder.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let callee = builder.declare_function("printf_like", callee_signature);
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut function = builder.function("caller", signature);
    let entry = function.create_block();
    let x = function.add_block_param(entry, Ty::I64);
    function.switch_to_block(entry);
    let result = function.call(callee, vec![x, x]);
    function.ret(vec![result]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn assert_refused(directory: &Path, args: &[&str], tag: &str, output_name: &str) {
    let output = run(directory, args);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{args:?} must fail: {stderr}");
    assert!(stderr.contains(tag), "{args:?}: {stderr}");
    assert!(
        !directory.join(output_name).exists(),
        "{args:?}: a refused compile must not publish {output_name}"
    );
}

#[test]
fn native_cli_refuses_variadic_definitions_and_byval_by_name() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("variadic.tmbc"),
        encode_tmbc(&variadic_definition()).unwrap(),
    )
    .unwrap();
    fs::write(
        directory.path().join("byval.tmbc"),
        encode_tmbc(&byval_definition(Ty::I64)).unwrap(),
    )
    .unwrap();
    for target in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        assert_refused(
            directory.path(),
            &[
                "--target",
                target,
                "-c",
                "-o",
                "variadic.o",
                "variadic.tmbc",
            ],
            "[TCG-VARIADIC-DEFINITION]",
            "variadic.o",
        );
        assert_refused(
            directory.path(),
            &["--target", target, "-c", "-o", "byval.o", "byval.tmbc"],
            "[TCG-BYVAL-ABI]",
            "byval.o",
        );
    }
}

#[test]
fn native_cli_still_compiles_variadic_calls() {
    let directory = tempfile::tempdir().unwrap();
    for target in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        // The call crosses an FFI boundary (`printf_like` is a bodyless
        // declaration), so the module pins the target it is compiled for
        // (`TargetInfoRequired`; every ingestion entry refuses what trust-ir's
        // validator refuses, WS7.3).
        let mut call = variadic_call();
        call.target_info = Some(trust_ir::TargetInfo {
            triple: target.into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        fs::write(
            directory.path().join("call.tmbc"),
            encode_tmbc(&call).unwrap(),
        )
        .unwrap();
        let output = run(
            directory.path(),
            &["--target", target, "-c", "-o", "call.o", "call.tmbc"],
        );
        assert!(
            output.status.success(),
            "{target}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            !fs::read(directory.path().join("call.o"))
                .unwrap()
                .is_empty()
        );
        fs::remove_file(directory.path().join("call.o")).unwrap();
    }
}

#[test]
fn wasm_cli_refuses_variadic_definitions_and_byval_by_name() {
    let directory = tempfile::tempdir().unwrap();
    let mut variadic = variadic_definition();
    variadic.target_info = Some(wasm::wasm32_target_info());
    let mut byval = byval_definition(Ty::I32);
    byval.target_info = Some(wasm::wasm32_target_info());
    fs::write(
        directory.path().join("variadic.tmbc"),
        encode_tmbc(&variadic).unwrap(),
    )
    .unwrap();
    fs::write(
        directory.path().join("byval.tmbc"),
        encode_tmbc(&byval).unwrap(),
    )
    .unwrap();
    assert_refused(
        directory.path(),
        &[
            "--target",
            "wasm32-unknown-unknown",
            "-o",
            "variadic.wasm",
            "variadic.tmbc",
        ],
        "[TCG-VARIADIC-DEFINITION]",
        "variadic.wasm",
    );
    assert_refused(
        directory.path(),
        &[
            "--target",
            "wasm32-unknown-unknown",
            "-o",
            "byval.wasm",
            "byval.tmbc",
        ],
        "[TCG-BYVAL-ABI]",
        "byval.wasm",
    );
}
