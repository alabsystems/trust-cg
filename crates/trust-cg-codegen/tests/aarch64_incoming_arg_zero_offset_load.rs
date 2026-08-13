#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, Target};

const ENTRY_NAME: &str = "__incoming_arg_zero_offset_load";
const INCOMING_ARG_ZERO_OFFSET_LOAD_TRUST_IR: &str = r#"
; trust_ir text format v1
module "incoming_arg_zero_offset_load"
target "aarch64-apple-darwin" 8 little

functy.0 = (ptr, ptr, u32, ptr, u32, ptr, u32, ptr, u32) -> ()

fn @__incoming_arg_zero_offset_load(functy.0) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: ptr, %4: u32, %5: ptr, %6: u32, %7: ptr, %8: u32):
    %9 = const u32 0
    %10 = gep i64, ptr %1, %9
    %11 = load i64, ptr %10
    %12 = const u64 0
    %13 = gep u8, ptr %0, %12
    store i64 %11, ptr %13
    %14 = const u64 8
    %15 = gep u8, ptr %0, %14
    store u32 %8, ptr %15
    ret
}
"#;

type EntryFn = extern "C" fn(*mut u8, *const i64, u32, *mut u8, u32, *mut u8, u32, *mut u8, u32);

fn read_i64(bytes: &[u8], offset: usize) -> i64 {
    i64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}

#[test]
fn incoming_stack_arg_does_not_rewrite_following_zero_offset_load() {
    let module = trust_ir::parser::parse_module(INCOMING_ARG_ZERO_OFFSET_LOAD_TRUST_IR)
        .expect("incoming-arg regression fixture must parse");
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = OptLevel::O1;
    let buffer = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("incoming-arg regression fixture must JIT at O1")
        .buffer;
    let raw = buffer
        .get_fn_ptr_bound(ENTRY_NAME)
        .expect("entry symbol should be present")
        .as_ptr();
    let entry: EntryFn = unsafe { std::mem::transmute(raw) };

    let state = [2_i64, 1, 0, 0, 0, 0, 0, 0, 77];
    let mut out = [0_u8; 16];
    entry(
        out.as_mut_ptr(),
        state.as_ptr(),
        state.len() as u32,
        std::ptr::null_mut(),
        0,
        std::ptr::null_mut(),
        0,
        std::ptr::null_mut(),
        123,
    );

    assert_eq!(
        read_i64(&out, 0),
        2,
        "load must read state[0], not state[8]"
    );
    assert_eq!(read_u32(&out, 8), 123, "ninth argument remains readable");
}
