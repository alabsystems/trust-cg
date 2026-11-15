// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Unwind-built driver for the abort-built region frames (`regions.rs`).
//!
//! `regions_driver <frame> <mask> <catch> <arg>`: call the C-unwind export
//! `<frame>(arg)`, inside `catch_unwind` when `catch` is 1. The callback's
//! N-th call panics when bit N-1 of `mask` is set.
use std::any::Any;
use std::io::{self, Write};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

unsafe extern "C-unwind" {
    fn region_direct(x: u64) -> u64;
    fn region_indirect(x: u64) -> u64;
    fn region_dyn(x: u64) -> u64;
    fn region_c_pointer(x: u64) -> u64;
    fn region_indirect_first(x: u64) -> u64;
    fn region_two_guards(x: u64) -> u64;
    fn region_loop(x: u64) -> u64;
    fn region_box_dyn_guard(x: u64) -> u64;
    fn region_guard_indirect(x: u64) -> u64;
    fn region_mixed(x: u64) -> u64;
    fn region_between_invokes(x: u64) -> u64;
    fn region_per_region(x: u64) -> u64;
    fn region_memcmp(x: u64) -> u64;
    fn region_array_fill(x: u64) -> u64;
    fn region_array_fill_large(x: u64) -> u64;
    fn region_memset(x: u64) -> u64;
    fn region_fma(x: u64) -> u64;
    fn region_powi(x: u64) -> u64;
    fn region_sin_constant(x: u64) -> u64;
    fn region_sin_runtime(x: u64) -> u64;
    fn region_i128_checked_mul(x: u64) -> u64;
    fn region_i128_div(x: u64) -> u64;
    fn region_rotate(x: u64) -> u64;
    fn region_print(x: u64) -> u64;
    fn region_tail(x: u64) -> u64;
    fn region_u128_div_literal(x: u64) -> u64;
    fn region_u128_narrow_div(x: u64) -> u64;
    fn region_dead_f64_to_i128(x: u64) -> u64;
    fn region_fill_folded(x: u64) -> u64;
    fn region_sin_derived(x: u64) -> u64;
    fn region_tls_constant(x: u64) -> u64;
    fn region_fn_pointer_local(x: u64) -> u64;
    fn region_fn_pointer_static(x: u64) -> u64;
    fn region_dyn_known(x: u64) -> u64;
    fn region_box_dyn_fn(x: u64) -> u64;
    fn region_inlined_pad(x: u64) -> u64;
    fn region_fn_pointer_table(x: u64) -> u64;
    fn region_fn_pointer_closure(x: u64) -> u64;
    fn region_box_dyn_opaque(x: u64) -> u64;
    fn region_fn_pointer_param(x: u64) -> u64;
    fn region_closure_param(x: u64) -> u64;
    fn region_dyn_param(x: u64) -> u64;
    fn region_box_dyn_param(x: u64) -> u64;
    fn region_closure_raw_written(x: u64) -> u64;
    fn region_pin_dyn(x: u64) -> u64;
    fn region_u128_const_div(x: u64) -> u64;
    fn region_f64_const_rem(x: u64) -> u64;
    fn region_u128_self_div(x: u64) -> u64;
    fn region_u128_from_const_div(x: u64) -> u64;
    fn region_slice_len_div(x: u64) -> u64;
    fn region_field_raw_written(x: u64) -> u64;
}

static MASK: AtomicU64 = AtomicU64::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static HOOKS: AtomicUsize = AtomicUsize::new(0);

// Hooks and callbacks never assert or exit: only the panic runtime may end
// the process. An I/O failure is visible as a missing line.
fn trace(arguments: std::fmt::Arguments<'_>) {
    let mut output = io::stdout().lock();
    let _ = output.write_fmt(arguments);
    let _ = output.flush();
}

#[unsafe(no_mangle)]
pub extern "C" fn terminate_region_record_drop(id: u64) {
    trace(format_args!("DROP={id}\n"));
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn terminate_region_callback(id: u64) {
    callback(id);
}

/// The same callback through the Rust ABI, which the abort-built frames
/// declare `nounwind`.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn terminate_region_rust_callback(id: u64) {
    callback(id);
}

/// The Rust-ABI callback returning a value, the last call of a frame.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn terminate_region_rust_callback_ret(id: u64) -> u64 {
    callback(id);
    id * 7
}

fn callback(id: u64) {
    let sequence = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
    trace(format_args!("CALLBACK id={id} seq={sequence}\n"));
    if sequence < 64 && MASK.load(Ordering::SeqCst) & (1 << (sequence - 1)) != 0 {
        panic!("region callback panic");
    }
}

fn payload_text(payload: &(dyn Any + Send)) -> &str {
    if let Some(text) = payload.downcast_ref::<&str>() {
        text
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text
    } else {
        "<non-string panic payload>"
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let [_, frame, mask, catch, arg] = args.as_slice() else {
        panic!("usage: regions_driver <frame> <mask> <catch> <arg>");
    };
    MASK.store(mask.parse().unwrap(), Ordering::SeqCst);
    let catch = catch == "1";
    let arg: u64 = arg.parse().unwrap();
    std::panic::set_hook(Box::new(|info| {
        let sequence = HOOKS.fetch_add(1, Ordering::SeqCst) + 1;
        let (file, line, column) = info
            .location()
            .map(|site| (site.file(), site.line(), site.column()))
            .unwrap_or(("<missing>", 0, 0));
        let file = file.rsplit('/').next().unwrap_or(file);
        trace(format_args!(
            "HOOK seq={sequence} payload={:?} at={file}:{line}:{column}\n",
            payload_text(info.payload())
        ));
    }));
    let frame = frame.clone();
    let run = move || unsafe {
        match frame.as_str() {
            "direct" => region_direct(arg),
            "indirect" => region_indirect(arg),
            "dyn" => region_dyn(arg),
            "c_pointer" => region_c_pointer(arg),
            "indirect_first" => region_indirect_first(arg),
            "two_guards" => region_two_guards(arg),
            "loop" => region_loop(arg),
            "box_dyn_guard" => region_box_dyn_guard(arg),
            "guard_indirect" => region_guard_indirect(arg),
            "mixed" => region_mixed(arg),
            "between_invokes" => region_between_invokes(arg),
            "per_region" => region_per_region(arg),
            "memcmp" => region_memcmp(arg),
            "array_fill" => region_array_fill(arg),
            "array_fill_large" => region_array_fill_large(arg),
            "memset" => region_memset(arg),
            "fma" => region_fma(arg),
            "powi" => region_powi(arg),
            "sin_constant" => region_sin_constant(arg),
            "sin_runtime" => region_sin_runtime(arg),
            "i128_checked_mul" => region_i128_checked_mul(arg),
            "i128_div" => region_i128_div(arg),
            "rotate" => region_rotate(arg),
            "print" => region_print(arg),
            "tail" => region_tail(arg),
            "u128_div_literal" => region_u128_div_literal(arg),
            "u128_narrow_div" => region_u128_narrow_div(arg),
            "dead_f64_to_i128" => region_dead_f64_to_i128(arg),
            "fill_folded" => region_fill_folded(arg),
            "sin_derived" => region_sin_derived(arg),
            "tls_constant" => region_tls_constant(arg),
            "fn_pointer_local" => region_fn_pointer_local(arg),
            "fn_pointer_static" => region_fn_pointer_static(arg),
            "dyn_known" => region_dyn_known(arg),
            "box_dyn_fn" => region_box_dyn_fn(arg),
            "inlined_pad" => region_inlined_pad(arg),
            "fn_pointer_table" => region_fn_pointer_table(arg),
            "fn_pointer_closure" => region_fn_pointer_closure(arg),
            "box_dyn_opaque" => region_box_dyn_opaque(arg),
            "fn_pointer_param" => region_fn_pointer_param(arg),
            "closure_param" => region_closure_param(arg),
            "dyn_param" => region_dyn_param(arg),
            "box_dyn_param" => region_box_dyn_param(arg),
            "closure_raw_written" => region_closure_raw_written(arg),
            "pin_dyn" => region_pin_dyn(arg),
            "u128_const_div" => region_u128_const_div(arg),
            "f64_const_rem" => region_f64_const_rem(arg),
            "u128_self_div" => region_u128_self_div(arg),
            "u128_from_const_div" => region_u128_from_const_div(arg),
            "slice_len_div" => region_slice_len_div(arg),
            "field_raw_written" => region_field_raw_written(arg),
            _ => panic!("unknown region frame"),
        }
    };
    if catch {
        let result = std::panic::catch_unwind(run);
        trace(format_args!(
            "AFTER caught={} value={:?} hooks={} calls={}\n",
            result.is_err(),
            result.as_ref().ok(),
            HOOKS.load(Ordering::SeqCst),
            CALLS.load(Ordering::SeqCst)
        ));
    } else {
        let value = run();
        trace(format_args!(
            "AFTER value={value} hooks={} calls={}\n",
            HOOKS.load(Ordering::SeqCst),
            CALLS.load(Ordering::SeqCst)
        ));
    }
    std::process::exit(0);
}
