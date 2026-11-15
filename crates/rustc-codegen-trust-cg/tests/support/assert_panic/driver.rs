// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use assert_panic_callee as callee;
use std::any::Any;
use std::io::Write;
use std::sync::Mutex;

type Site = (String, u32, u32);
type Observation = (String, Site, bool);

static DROPS: Mutex<Vec<u64>> = Mutex::new(Vec::new());
static EXPECTED: Mutex<Option<(String, Site)>> = Mutex::new(None);
static HOOK: Mutex<Option<Observation>> = Mutex::new(None);
static WORD: u64 = 47;
static BYTE: u8 = 59;

#[unsafe(no_mangle)]
pub extern "C" fn assert_panic_record_drop(id: u64) {
    DROPS.lock().unwrap().push(id);
    println!("DROP={id}");
    std::io::stdout().flush().unwrap();
}

fn payload(value: &(dyn Any + Send)) -> Option<&str> {
    value
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| value.downcast_ref::<&str>().copied())
}

fn install_hook() {
    std::panic::set_hook(Box::new(|info| {
        // A wrong payload must produce HOOK_OK=0, not panic inside this hook:
        // a double panic could otherwise disguise the mismatch as SIGABRT.
        let message = payload(info.payload()).unwrap_or("<unsupported payload>");
        let site = info.location().map_or_else(
            || ("<missing location>".to_owned(), 0, 0),
            |at| (at.file().to_owned(), at.line(), at.column()),
        );
        let valid = EXPECTED
            .lock()
            .unwrap()
            .as_ref()
            .is_some_and(|(text, at)| text == message && at == &site);
        println!(
            "HOOK_OK={} PAYLOAD={message:?} SITE={site:?}",
            u8::from(valid)
        );
        std::io::stdout().flush().unwrap();
        *HOOK.lock().unwrap() = Some((message.to_owned(), site, valid));
    }));
}

fn finish(
    result: std::thread::Result<u64>,
    expected_message: String,
    expected_site: Site,
    guard: u64,
    must_abort: bool,
) {
    if must_abort {
        println!("AFTER_ASSERT: the aborting assertion returned or was caught");
        std::process::exit(4);
    }
    let caught = result.expect_err("the failing source assertion returned normally");
    assert_eq!(payload(&*caught), Some(expected_message.as_str()));
    let observed = HOOK.lock().unwrap().take().expect("the panic hook ran");
    assert_eq!(observed, (expected_message, expected_site, true));
    assert_eq!(&*DROPS.lock().unwrap(), &[guard]);
    println!("CAUGHT_OK=1");
}

fn controls() {
    assert_eq!(callee::assert_add(10, 20), 30);
    assert_eq!(callee::assert_sub(30, 10), 20);
    assert_eq!(callee::assert_mul(6, 7), 42);
    assert_eq!(callee::assert_div_overflow(100, 4), 25);
    assert_eq!(callee::assert_rem_overflow(103, 4), 3);
    assert_eq!(callee::assert_shl(2, 4), 32);
    assert_eq!(callee::assert_shr(256, 4), 16);
    assert_eq!(callee::assert_neg(-7), 7);
    assert_eq!(callee::assert_div_zero(80, 5), 16);
    assert_eq!(callee::assert_rem_zero(83, 5), 3);
    assert_eq!(callee::assert_bounds(2), 30);
    assert_eq!(unsafe { callee::assert_misaligned(&WORD) }, 47);
    assert_eq!(unsafe { callee::assert_null(&WORD) }, 47);
    assert_eq!(unsafe { callee::assert_null_reference(&BYTE) }, 59);
    assert_eq!(callee::assert_bounds_chain(2), 30);
    assert_eq!(callee::assert_inline_bounds(2), 30);
    assert_eq!(callee::assert_plain_div(80, 5), 16);
    assert_eq!(
        &*DROPS.lock().unwrap(),
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 11, 15, 16]
    );
    println!("CONTROLS_OK=17");
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let case = arguments.get(1).expect("a mandatory case").as_str();
    if case == "controls" {
        controls();
        return;
    }
    let must_abort = arguments.get(2).expect("a mandatory outcome") == "abort";
    install_hook();

    // Construct the call in the macro so its expected line/column and the
    // #[track_caller] call share the invocation span, as the existing tracked
    // panic differential does. The actual Rust signature comes from rlib
    // metadata; no hand-declared panic or hidden-location ABI is involved.
    macro_rules! call_at {
        ($name:ident($($argument:expr),*), $message:expr, $guard:expr, $site:expr) => {{
            let message: String = $message.into();
            let site: Site = $site;
            *EXPECTED.lock().unwrap() = Some((message.clone(), site.clone()));
            let result = std::panic::catch_unwind(|| unsafe { callee::$name($($argument),*) });
            finish(result, message, site, $guard, must_abort);
        }};
    }
    macro_rules! call {
        ($name:ident($($argument:expr),*), $message:expr, $guard:expr) => {
            call_at!(
                $name($($argument),*),
                $message,
                $guard,
                (file!().to_owned(), line!(), column!())
            )
        };
    }

    match case {
        "add" => call!(assert_add(u64::MAX, 1), "attempt to add with overflow", 1),
        "sub" => call!(assert_sub(0, 1), "attempt to subtract with overflow", 2),
        "mul" => call!(
            assert_mul(u64::MAX, 2),
            "attempt to multiply with overflow",
            3
        ),
        "div_overflow" => call!(
            assert_div_overflow(i64::MIN, -1),
            "attempt to divide with overflow",
            4
        ),
        "rem_overflow" => call!(
            assert_rem_overflow(i64::MIN, -1),
            "attempt to calculate the remainder with overflow",
            5
        ),
        "shl" => call!(assert_shl(1, 64), "attempt to shift left with overflow", 6),
        "shr" => call!(assert_shr(1, 64), "attempt to shift right with overflow", 7),
        "neg" => call!(assert_neg(i64::MIN), "attempt to negate with overflow", 8),
        "div_zero" => call!(assert_div_zero(80, 0), "attempt to divide by zero", 9),
        "rem_zero" => call!(
            assert_rem_zero(83, 0),
            "attempt to calculate the remainder with a divisor of zero",
            10
        ),
        "bounds" => call!(
            assert_bounds(9),
            "index out of bounds: the len is 4 but the index is 9",
            11
        ),
        "bounds_max" => call!(
            assert_bounds(usize::MAX),
            format!(
                "index out of bounds: the len is 4 but the index is {}",
                usize::MAX
            ),
            11
        ),
        "misaligned" => call!(
            assert_misaligned(1usize as *const u64),
            "misaligned pointer dereference: address must be a multiple of 0x8 but is 0x1",
            12
        ),
        "null" => call!(
            assert_null(core::ptr::null()),
            "null pointer dereference occurred",
            13
        ),
        "null_reference" => call!(
            assert_null_reference(core::ptr::null()),
            "null reference produced",
            14
        ),
        "chain" => call!(
            assert_bounds_chain(9),
            "index out of bounds: the len is 4 but the index is 9",
            11
        ),
        "inline" => call!(
            assert_inline_bounds(9),
            "index out of bounds: the len is 4 but the index is 9",
            15
        ),
        "boundary" => call_at!(
            assert_plain_div(80, 0),
            "attempt to divide by zero",
            16,
            (callee::SOURCE_FILE.to_owned(), callee::PLAIN_DIV_LINE, 5)
        ),
        _ => panic!("unknown mandatory case {case}"),
    }
}
