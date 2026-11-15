// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use std::any::Any;
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

#[cfg(not(terminate_foreign_object))]
use terminate_panic_callee as callee;

// These declarations match actual source-defined C-unwind exports, not Rust or panic
// entry ABIs. Their metadata types are checked in an abort-built consumer.
#[cfg(terminate_foreign_object)]
unsafe extern "C-unwind" {
    fn terminate_foreign_drop_control(value: u64) -> u64;
    fn terminate_foreign_guard_control(value: u64) -> u64;
}

const SOURCE_PAYLOAD: &str = "attempt to divide by zero";
const CALLBACK_PAYLOAD: &str = "panic from LLVM cleanup callback";
const ABI_REASON: &str = "panic in a function that cannot unwind";
const CLEANUP_REASON: &str = "panic in a destructor during cleanup";

static CASE: AtomicU8 = AtomicU8::new(0);
static PANIC_ON_DROP: AtomicBool = AtomicBool::new(false);
static HOOKS: AtomicUsize = AtomicUsize::new(0);
static DROPS: AtomicUsize = AtomicUsize::new(0);
static CALLBACKS: AtomicUsize = AtomicUsize::new(0);
static BAD: AtomicBool = AtomicBool::new(false);

// Returning hooks must not assert, panic, or exit: only the actual Rust panic
// runtime may produce the tested terminal signal. I/O failures mark the trace
// bad without causing a panic while a hook is running.
fn trace(arguments: std::fmt::Arguments<'_>) {
    let mut output = io::stdout().lock();
    if output.write_fmt(arguments).is_err() || output.flush().is_err() {
        BAD.store(true, Ordering::SeqCst);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn terminate_panic_record_drop(id: u64) {
    DROPS.fetch_add(1, Ordering::SeqCst);
    if id != 7 {
        BAD.store(true, Ordering::SeqCst);
    }
    trace(format_args!("DROP={id}\n"));
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn terminate_panic_cleanup_callback(id: u64) {
    let sequence = CALLBACKS.fetch_add(1, Ordering::SeqCst) + 1;
    if id != 7 {
        BAD.store(true, Ordering::SeqCst);
    }
    trace(format_args!("CALLBACK={id}\n"));
    // Case 4 throws from the source body's first foreign call, but returns
    // from the callback reached by its cleanup Drop. Case 5 throws from both.
    // The original cases keep exactly their PANIC_ON_DROP behavior.
    let should_panic = match CASE.load(Ordering::SeqCst) {
        4 => sequence == 1,
        5 => true,
        _ => PANIC_ON_DROP.load(Ordering::SeqCst),
    };
    if should_panic {
        panic!("panic from LLVM cleanup callback");
    }
}
const CALLBACK_PANIC_LINE: u32 = line!() - 3;
const CALLBACK_PANIC_COLUMN: u32 = 9;

fn payload_text(payload: &(dyn Any + Send)) -> &str {
    if let Some(text) = payload.downcast_ref::<&str>() {
        text
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text
    } else {
        "<non-string panic payload>"
    }
}

fn install_hook() {
    std::panic::set_hook(Box::new(|info| {
        let sequence = HOOKS.fetch_add(1, Ordering::SeqCst) + 1;
        let case = CASE.load(Ordering::SeqCst);
        let payload = payload_text(info.payload());
        let location = info.location();
        let (file, line, column) = location
            .map(|site| (site.file(), site.line(), site.column()))
            .unwrap_or(("<missing>", 0, 0));
        let valid = match (case, sequence) {
            #[cfg(not(terminate_foreign_object))]
            (1, 1) => {
                payload == SOURCE_PAYLOAD
                    && file == callee::SOURCE_FILE
                    && line == callee::ABI_ASSERT_LINE
                    && column == callee::ABI_ASSERT_COLUMN
            }
            #[cfg(not(terminate_foreign_object))]
            (2, 1) => {
                payload == SOURCE_PAYLOAD
                    && file == callee::SOURCE_FILE
                    && line == callee::CLEANUP_ASSERT_LINE
                    && column == callee::CLEANUP_ASSERT_COLUMN
            }
            (2, 2) => {
                payload == CALLBACK_PAYLOAD
                    && file == file!()
                    && line == CALLBACK_PANIC_LINE
                    && column == CALLBACK_PANIC_COLUMN
            }
            (1, 2) => payload == ABI_REASON && !file.is_empty() && line > 0 && column > 0,
            (2, 3) => payload == CLEANUP_REASON && !file.is_empty() && line > 0 && column > 0,
            (3..=5, 1) | (5, 2) => {
                payload == CALLBACK_PAYLOAD
                    && file == file!()
                    && line == CALLBACK_PANIC_LINE
                    && column == CALLBACK_PANIC_COLUMN
            }
            (3 | 4, 2) => payload == ABI_REASON && !file.is_empty() && line > 0 && column > 0,
            _ => false,
        };
        if !valid {
            BAD.store(true, Ordering::SeqCst);
        }
        trace(format_args!(
            "HOOK seq={sequence} valid={} payload={payload:?} file={file:?} line={line} column={column}\n",
            u8::from(valid)
        ));
        let terminal_sequence = match case {
            1 | 3 | 4 => 2,
            2 => 3,
            _ => 0,
        };
        if sequence == terminal_sequence {
            let expected_reason = if case == 2 {
                CLEANUP_REASON
            } else {
                ABI_REASON
            };
            let wrong_reason = payload != expected_reason;
            trace(format_args!("WRONG_REASON={}\n", u8::from(wrong_reason)));
        }
    }));
}

#[cfg(not(terminate_foreign_object))]
fn controls() {
    assert_eq!(callee::terminate_source_boundary(84, 4), 21);
    assert_eq!(callee::terminate_source_cleanup(84, 7), 12);
    assert_eq!(HOOKS.load(Ordering::SeqCst), 0);
    assert_eq!(DROPS.load(Ordering::SeqCst), 1);
    assert_eq!(CALLBACKS.load(Ordering::SeqCst), 1);
    assert!(!BAD.load(Ordering::SeqCst));
    trace(format_args!("CONTROLS_OK=2 HOOKS=0 DROPS=1 CALLBACKS=1\n"));
}

#[cfg(terminate_foreign_object)]
fn foreign_controls() {
    assert_eq!(unsafe { terminate_foreign_drop_control(84) }, 12);
    assert_eq!(unsafe { terminate_foreign_guard_control(57) }, 57);
    assert_eq!(HOOKS.load(Ordering::SeqCst), 0);
    assert_eq!(DROPS.load(Ordering::SeqCst), 2);
    assert_eq!(CALLBACKS.load(Ordering::SeqCst), 3);
    assert!(!BAD.load(Ordering::SeqCst));
    trace(format_args!(
        "FOREIGN_CONTROLS_OK=2 HOOKS=0 DROPS=2 CALLBACKS=3\n"
    ));
}

#[cfg(not(terminate_foreign_object))]
fn main() {
    let case = std::env::args().nth(1).expect("required fixture case");
    install_hook();
    if case == "controls" {
        controls();
        return;
    }
    let case_number = match case.as_str() {
        "abi" => 1,
        "cleanup" => 2,
        _ => panic!("unknown termination fixture case"),
    };
    CASE.store(case_number, Ordering::SeqCst);
    PANIC_ON_DROP.store(case_number == 2, Ordering::SeqCst);
    let result = std::panic::catch_unwind(|| match case_number {
        1 => callee::terminate_source_boundary(84, 0),
        2 => callee::terminate_source_cleanup(84, 0),
        _ => unreachable!(),
    });
    // An incorrect catch or return is observable and never accepted as abort.
    trace(format_args!(
        "AFTER_TERMINATE caught={} hooks={} drops={} callbacks={} bad={}\n",
        result.is_err(),
        HOOKS.load(Ordering::SeqCst),
        DROPS.load(Ordering::SeqCst),
        CALLBACKS.load(Ordering::SeqCst),
        BAD.load(Ordering::SeqCst)
    ));
    std::process::exit(4);
}

#[cfg(terminate_foreign_object)]
fn main() {
    let case = std::env::args()
        .nth(1)
        .expect("required mixed-strategy fixture case");
    install_hook();
    if case == "foreign-controls" {
        foreign_controls();
        return;
    }
    let case_number = match case.as_str() {
        "foreign-drop" => 3,
        "foreign-guard" => 4,
        "foreign-nested" => 5,
        _ => panic!("unknown foreign-abort fixture case"),
    };
    CASE.store(case_number, Ordering::SeqCst);
    PANIC_ON_DROP.store(case_number == 3, Ordering::SeqCst);
    let result = std::panic::catch_unwind(|| unsafe {
        match case_number {
            3 => terminate_foreign_drop_control(84),
            4 | 5 => terminate_foreign_guard_control(84),
            _ => unreachable!(),
        }
    });
    trace(format_args!(
        "AFTER_TERMINATE caught={} hooks={} drops={} callbacks={} bad={}\n",
        result.is_err(),
        HOOKS.load(Ordering::SeqCst),
        DROPS.load(Ordering::SeqCst),
        CALLBACKS.load(Ordering::SeqCst),
        BAD.load(Ordering::SeqCst)
    ));
    std::process::exit(4);
}
