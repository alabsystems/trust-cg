unsafe extern "Rust" {
    fn option128_read(value: Option<u128>, fallback: u128) -> u128;
    fn option128_after_one(prefix: u64, value: Option<u128>, suffix: u64) -> u128;
    fn option128_after_five(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
unsafe extern "C" {
    fn option128_call_llvm(value: u128, some: bool, prefix: u64, fallback: u128) -> u128;
}
#[unsafe(no_mangle)]
pub fn llvm_option128(prefix: u64, value: Option<u128>, fallback: u128) -> u128 {
    value.unwrap_or(fallback).wrapping_add(prefix as u128)
}
fn main() {
    let mut checks = 0;
    for i in 0..256u64 {
        let value = ((i.wrapping_mul(0x9e3779b97f4a7c15) as u128) << 64)
            | (i.wrapping_mul(0xd6e8feb86659fd93) as u128);
        let fallback = !value;
        for some in [false, true] {
            let opt = if some { Some(value) } else { None };
            let expected = if some { value } else { fallback };
            let p = i.wrapping_mul(97);
            let suffix = i.wrapping_add(123);
            unsafe {
                assert_eq!(option128_read(opt, fallback), expected);
                assert_eq!(
                    option128_after_one(p, opt, suffix),
                    (if some { value } else { p as u128 }).wrapping_add(suffix as u128)
                );
                assert_eq!(
                    option128_after_five(p, 2, 3, 5, 7, opt, suffix),
                    (if some { value } else { p as u128 })
                        .wrapping_add(17)
                        .wrapping_add(suffix as u128)
                );
                assert_eq!(
                    option128_call_llvm(value, some, p, fallback),
                    expected.wrapping_add(p as u128)
                );
                checks += 4;
            }
        }
    }
    println!("PASS option128_abi checks={checks}");
}
