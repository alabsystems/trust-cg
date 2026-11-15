unsafe extern "C-unwind" {
    fn write_then_unwind(
        cb: unsafe extern "C-unwind" fn(u64) -> u64,
        a: u64,
        b: u64,
        x: u64,
        out: *mut u64,
    ) -> u64;
}
unsafe extern "C-unwind" fn callback(x: u64) -> u64 {
    if cfg!(panic = "unwind") && x & 7 == 3 {
        panic!("reference callback");
    }
    x.wrapping_mul(13)
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut panics = 0;
    for x in 0..1024u64 {
        let a = x.wrapping_mul(0xf00e00d00c00b00a);
        let b = !a;
        let expected = (a ^ x).wrapping_add(41) ^ b.wrapping_add(x).wrapping_mul(17);
        let mut output = [0u64; 2];
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            write_then_unwind(callback, a, b, x, output.as_mut_ptr())
        }));
        if cfg!(panic = "unwind") && x & 7 == 3 {
            assert!(result.is_err());
            panics += 1;
        } else {
            assert_eq!(result.unwrap(), expected ^ x.wrapping_mul(13));
        }
        assert_eq!(output[0], expected.rotate_left(9), "seed {x}");
        assert_eq!(output[1], 1);
    }
    println!("PASS variadic_reference_unwind checks=3072 panics={panics}");
}
