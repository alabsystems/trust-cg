use std::os::unix::process::ExitStatusExt;
unsafe extern "Rust" {
    fn generic_valid(seed: u64) -> u64;
    fn generic_uninit_bool();
    fn generic_invalid(case: u32);
}

struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        std::process::exit(93);
    }
}

/// rustc's exact message for each invalid case (case 5 is the strict-init
/// `bool`).
fn expected(case: u32) -> &'static str {
    match case {
        0 => "attempted to zero-initialize type `&u8`, which is invalid",
        1 => "attempted to zero-initialize type `core::num::nonzero::NonZero<u64>`, which is invalid",
        2 => "attempted to instantiate uninhabited type `Empty`",
        3 => "attempted to leave type `&u8` uninitialized, which is invalid",
        4 => "attempted to zero-initialize type `fn(u64) -> u64`, which is invalid",
        5 => "attempted to leave type `bool` uninitialized, which is invalid",
        _ => std::process::exit(94),
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
            if message != expected(case) {
                eprintln!("unexpected hook payload: {message}");
                std::process::exit(95);
            }
            println!("HOOK generic case={case}");
            std::io::stdout().flush().unwrap();
        }));
        let _guard = Guard;
        unsafe {
            if case == 5 {
                generic_uninit_bool();
            } else {
                generic_invalid(case);
            }
        }
        std::process::exit(96);
    }
    for seed in 0..4096u64 {
        assert_eq!(
            unsafe { generic_valid(seed) },
            seed.rotate_left(29) ^ 0x0f0e_0d0c_0b0a_0908
        );
    }
    let cases = if cfg!(strict_init) { 6 } else { 5 };
    for case in 0..cases {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .arg(case.to_string())
            .output()
            .unwrap();
        assert_eq!(result.status.signal(), Some(6), "case={case}: {result:?}");
        assert_eq!(
            result.stdout,
            format!("HOOK generic case={case}\n").as_bytes(),
            "case={case}: {result:?}"
        );
    }
    if !cfg!(strict_init) {
        unsafe { generic_uninit_bool() };
    }
    println!("PASS generic_validity checks=4096 aborts={cases}");
}
