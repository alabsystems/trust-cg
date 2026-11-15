use std::sync::Mutex;

mod runtime {
    unsafe extern "Rust" {
        #[track_caller]
        pub fn runtime_literal(message: &'static str) -> !;
        #[track_caller]
        pub fn runtime_formatted(value: u64) -> !;
        #[track_caller]
        pub fn runtime_guarded(value: u64) -> !;
        #[track_caller]
        pub fn runtime_arguments(args: core::fmt::Arguments<'_>) -> !;
        #[track_caller]
        pub fn runtime_nounwind(message: &'static str) -> !;
        #[track_caller]
        pub fn helper_literal(message: &'static str) -> !;
        #[track_caller]
        pub fn helper_formatted(value: u64) -> !;
    }
}

static DROPS: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
static SITE: Mutex<Option<(String, u32, u32)>> = Mutex::new(None);

#[unsafe(no_mangle)]
pub extern "C" fn runtime_drop(kind: u64, value: u64) {
    DROPS.lock().unwrap().push((kind, value));
}

fn payload(value: &(dyn core::any::Any + Send)) -> &str {
    if let Some(s) = value.downcast_ref::<String>() {
        s
    } else {
        value.downcast_ref::<&str>().unwrap()
    }
}

fn main() {
    if let Some(mode) = std::env::args().nth(1) {
        unsafe {
            match mode.as_str() {
                "literal" => runtime::runtime_literal("runtime abort literal"),
                "formatted" => runtime::runtime_formatted(18446744073709551615),
                "arguments" => runtime::runtime_arguments(format_args!("runtime argument={}", 37)),
                "nounwind" => runtime::runtime_nounwind("runtime cannot unwind"),
                _ => panic!("unknown mode"),
            }
        }
    }
    std::panic::set_hook(Box::new(|info| {
        let at = info.location().unwrap();
        *SITE.lock().unwrap() = Some((at.file().to_owned(), at.line(), at.column()));
    }));
    let mut checks = 0;
    macro_rules! check {
        ($name:ident($($arg:expr),*), $expected:expr, $drops:expr) => {{
            let p = std::panic::catch_unwind(|| unsafe { runtime::$name($($arg),*) }).unwrap_err();
            let actual = payload(&*p);
            if actual != $expected { eprintln!("expected={:?} actual={actual:?}", $expected); }
            assert_eq!(actual, $expected);
            let site = SITE.lock().unwrap().take().unwrap();
            assert_eq!((site.0.as_str(),site.1,site.2),(file!(),line!(),column!()));
            assert_eq!(&*DROPS.lock().unwrap(), $drops);
            DROPS.lock().unwrap().clear();
            checks += 1;
        }};
    }
    for i in 0..128u64 {
        let value = i.wrapping_mul(0x9e3779b97f4a7c15);
        let msg = if i % 2 == 0 {
            "first dynamic literal"
        } else {
            "second literal é"
        };
        check!(runtime_literal(msg), msg, &[]);
        check!(helper_literal(msg), msg, &[]);
        check!(helper_formatted(value), format!("helper={value}"), &[]);
        check!(runtime_formatted(value), format!("value={value}"), &[]);
        check!(
            runtime_guarded(value),
            format!("guard={value}"),
            &[(7, value)]
        );
        check!(
            runtime_arguments(format_args!("argument={value}")),
            format!("argument={value}"),
            &[]
        );
    }
    assert_eq!(checks, 768);
    println!("PASS panic_runtime checks={checks}");
}
