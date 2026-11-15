unsafe extern "C-unwind" {
    fn invoke_variadic(
        callback: unsafe extern "C-unwind" fn(u64) -> u64,
        value: u64,
        drops: *mut u64,
    ) -> u64;
}
unsafe extern "C-unwind" fn callback(value: u64) -> u64 {
    #[cfg(panic = "unwind")]
    if value & 7 == 3 {
        panic!("variadic callback");
    }
    value.wrapping_mul(0xf00e00d00c00b00a)
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut drops = 0;
    let mut panics = 0;
    for value in 0..1024 {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            invoke_variadic(callback, value, &mut drops)
        }));
        if cfg!(panic = "unwind") && value & 7 == 3 {
            assert!(result.is_err());
            panics += 1;
        } else {
            assert_eq!(result.unwrap(), value.wrapping_mul(0xf00e00d00c00b00a) ^ 23);
        }
        assert_eq!(drops, value + 1);
    }
    println!("PASS variadic_unwind checks=2048 panics={panics}");
}
