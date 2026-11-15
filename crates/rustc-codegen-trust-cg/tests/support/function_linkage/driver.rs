unsafe extern "Rust" {
    fn linkage_base(x: u64) -> u64;
    fn linkage_left(x: u64) -> u64;
    fn linkage_right(x: u64) -> u64;
    fn linkage_left_indirect(x: u64) -> u64;
    fn linkage_right_indirect(x: u64) -> u64;
    fn linkage_left_dynamic(x: u64) -> u64;
    fn linkage_right_dynamic(x: u64) -> u64;
    static LEFT_CALLBACK: fn(u64) -> u64;
    static RIGHT_CALLBACK: fn(u64) -> u64;
    static LEFT_CALLBACK_SLOT: &'static fn(u64) -> u64;
    static RIGHT_CALLBACK_SLOT: &'static fn(u64) -> u64;
}
fn oracle(x: u64) -> u64 {
    ((x << 13) | (x >> 51)).wrapping_add(0x7351aef926cb804d)
}
fn main() {
    unsafe {
        assert!(core::ptr::eq(LEFT_CALLBACK_SLOT, RIGHT_CALLBACK_SLOT));
    }
    let mut state = 0xdeadbeef01234567_u64;
    for i in 0..32768 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let x = if i < 64 { 1 << i } else { state };
        unsafe {
            for f in [
                linkage_base,
                linkage_left,
                linkage_right,
                LEFT_CALLBACK,
                RIGHT_CALLBACK,
                *LEFT_CALLBACK_SLOT,
                *RIGHT_CALLBACK_SLOT,
            ] {
                assert_eq!(f(x), oracle(x));
            }
            for f in [linkage_left_indirect, linkage_right_indirect] {
                assert_eq!(f(x), oracle(x) ^ oracle(x.wrapping_add(3)));
            }
            for f in [linkage_left_dynamic, linkage_right_dynamic] {
                assert_eq!(f(x), oracle(x ^ x.wrapping_mul(7)));
            }
        }
    }
    println!("function linkage: 360449 native checks");
}
