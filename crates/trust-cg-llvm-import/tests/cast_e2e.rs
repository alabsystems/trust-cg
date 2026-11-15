#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / cast_e2e.rs
//
// Regression coverage for WS2 imported integer cast chains, compiled for this
// host's explicit triple, linked with `cc` and run natively.

mod common;

use std::fs;
use std::process::Command;

use common::{
    compile_for_host, describe_status, link_with_cc, native_host_or_skip, unique_temp_dir,
};
use trust_cg_codegen::pipeline::OptLevel;

const LL_CASTTEST_TRUNC_I8: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

define i32 @test(i32 noundef %0) {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = trunc i32 %3 to i8
  %5 = zext i8 %4 to i32
  ret i32 %5
}

define i32 @main() {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = call i32 @test(i32 noundef 123456)
  %3 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %2)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...)
"#;

#[test]
fn ws2_casttest_trunc_i8_linked_binary_prints_64() {
    if !native_host_or_skip("ws2_casttest_trunc_i8_linked_binary_prints_64") {
        return;
    }

    let object = compile_for_host(LL_CASTTEST_TRUNC_I8, "ws2_casttest_trunc_i8", OptLevel::O0);
    let dir = unique_temp_dir("casttest-trunc-i8");
    let obj_path = dir.join("casttest.o");
    let bin_path = dir.join("casttest");
    fs::write(&obj_path, object).expect("write object");
    link_with_cc(&obj_path, &bin_path);

    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert!(
        output.status.success(),
        "linked binary failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "64\n");
}
