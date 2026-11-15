use std::os::unix::process::ExitStatusExt;
unsafe extern "Rust" {
    fn valid_checks(seed: u64) -> u64;
    fn zeroed_scalar() -> u64;
    fn zeroed_char() -> char;
    fn zeroed_bool() -> bool;
    fn zeroed_option() -> bool;
    fn invalid_check(case: u32);
    fn uninitialized_bool_policy();
}

struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        std::process::exit(93);
    }
}

fn main() {
    if let Some(case) = std::env::args().nth(1) {
        let case: u32 = case.parse().unwrap();
        std::panic::set_hook(Box::new(move |info| {
            use std::io::Write;
            let message = info
                .payload()
                .downcast_ref::<&str>()
                .copied()
                .or_else(|| info.payload().downcast_ref::<String>().map(String::as_str))
                .unwrap_or("");
            let (prefix, suffix) = match case {
                0 => (
                    "attempted to zero-initialize type `",
                    "&u8`, which is invalid",
                ),
                1 => (
                    "attempted to zero-initialize type `",
                    "NonZero<u64>`, which is invalid",
                ),
                2 => (
                    "attempted to zero-initialize type `",
                    "fn(u64) -> u64`, which is invalid",
                ),
                3 | 4 => ("attempted to instantiate uninhabited type `", "Empty`"),
                5 => (
                    "attempted to leave type `",
                    "&u8` uninitialized, which is invalid",
                ),
                6 => (
                    "attempted to leave type `",
                    "bool` uninitialized, which is invalid",
                ),
                _ => std::process::exit(94),
            };
            if !message.starts_with(prefix) || !message.ends_with(suffix) {
                eprintln!("unexpected hook payload: {message}");
                std::process::exit(95);
            }
            println!("HOOK validity case={case}");
            std::io::stdout().flush().unwrap();
        }));
        let _guard = Guard;
        unsafe {
            if case == 6 {
                uninitialized_bool_policy();
            } else {
                invalid_check(case);
            }
        }
        std::process::exit(96);
    }
    for seed in 0..4096u64 {
        unsafe {
            assert_eq!(
                valid_checks(seed),
                seed.rotate_left(17) ^ 0x1234567890abcdef
            );
            assert_eq!(zeroed_scalar(), 0);
            assert_eq!(zeroed_char(), '\0');
            assert!(!zeroed_bool());
            assert!(zeroed_option());
        }
    }
    for case in 0..6 {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .arg(case.to_string())
            .output()
            .unwrap();
        assert_eq!(result.status.signal(), Some(6), "case={case}: {result:?}");
        assert_eq!(
            result.stdout,
            format!("HOOK validity case={case}\n").as_bytes()
        );
    }
    if cfg!(strict_init) {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("6")
            .output()
            .unwrap();
        assert_eq!(
            result.status.signal(),
            Some(6),
            "strict-init bool: {result:?}"
        );
        assert_eq!(result.stdout, b"HOOK validity case=6\n");
    } else {
        unsafe {
            uninitialized_bool_policy();
        }
    }
    println!(
        "PASS intrinsic_validity checks=20480 aborts={}",
        if cfg!(strict_init) { 7 } else { 6 }
    );
}
