// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Unwind-built driver for the unwind-built region frames (`unwind_regions.rs`).
//!
//! `unwind_regions_driver <frame> <mask> <catch> <arg>`: call the C-unwind
//! export `uw_<frame>(arg)`, inside `catch_unwind` when `catch` is 1. The
//! callback's N-th call panics when bit N-1 of `mask` is set.
use std::any::Any;
use std::io::{self, Write};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

unsafe extern "C-unwind" {
    fn uw_padded_before(x: u64) -> u64;
    fn uw_padded_after(x: u64) -> u64;
    fn uw_padded_live(x: u64) -> u64;
    fn uw_no_pads(x: u64) -> u64;
    fn uw_between_shared(x: u64) -> u64;
    fn uw_between_foreign(x: u64) -> u64;
    fn uw_c_pointer(x: u64) -> u64;
    fn uw_c_pointer_known(x: u64) -> u64;
    fn uw_cleanup_calls_c(x: u64) -> u64;
    fn uw_cleanup_calls_c_inline(x: u64) -> u64;
    fn uw_padded_cu(x: u64) -> u64;
    fn uw_padded_rust(x: u64) -> u64;
    fn uw_libc_region(x: u64) -> u64;
    fn uw_libc_qsort(x: u64) -> u64;
    fn uw_libc_qsort_gap(x: u64) -> u64;
    fn uw_libc_qsort_unwinds(x: u64) -> u64;
    fn uw_rust_shares_region(x: u64) -> u64;
    fn uw_print_region(x: u64) -> u64;
    fn uw_resume_region(x: u64) -> u64;
    fn uw_bare_before(x: u64) -> u64;
    fn uw_inlinable_before(x: u64) -> u64;
    fn uw_rust_unprotected(x: u64) -> u64;
    fn uw_cu_unprotected(x: u64) -> u64;
    fn uw_rust_pointer_unprotected(x: u64) -> u64;
    fn uw_dyn_unprotected(x: u64) -> u64;
}

static MASK: AtomicU64 = AtomicU64::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static HOOKS: AtomicUsize = AtomicUsize::new(0);

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

#[unsafe(no_mangle)]
#[inline(never)]
pub fn terminate_region_rust_callback(id: u64) {
    callback(id);
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
        panic!("usage: unwind_regions_driver <frame> <mask> <catch> <arg>");
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
            "padded_before" => uw_padded_before(arg),
            "padded_after" => uw_padded_after(arg),
            "padded_live" => uw_padded_live(arg),
            "no_pads" => uw_no_pads(arg),
            "between_shared" => uw_between_shared(arg),
            "between_foreign" => uw_between_foreign(arg),
            "c_pointer" => uw_c_pointer(arg),
            "c_pointer_known" => uw_c_pointer_known(arg),
            "cleanup_calls_c" => uw_cleanup_calls_c(arg),
            "cleanup_calls_c_inline" => uw_cleanup_calls_c_inline(arg),
            "padded_cu" => uw_padded_cu(arg),
            "padded_rust" => uw_padded_rust(arg),
            "libc_region" => uw_libc_region(arg),
            "libc_qsort" => uw_libc_qsort(arg),
            "libc_qsort_gap" => uw_libc_qsort_gap(arg),
            "libc_qsort_unwinds" => uw_libc_qsort_unwinds(arg),
            "rust_shares_region" => uw_rust_shares_region(arg),
            "print_region" => uw_print_region(arg),
            "resume_region" => uw_resume_region(arg),
            "bare_before" => uw_bare_before(arg),
            "inlinable_before" => uw_inlinable_before(arg),
            "rust_unprotected" => uw_rust_unprotected(arg),
            "cu_unprotected" => uw_cu_unprotected(arg),
            "rust_pointer_unprotected" => uw_rust_pointer_unprotected(arg),
            "dyn_unprotected" => uw_dyn_unprotected(arg),
            _ => panic!("unknown frame"),
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
