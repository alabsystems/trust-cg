#![no_std]
#[unsafe(no_mangle)]
pub fn option128_read(value: Option<u128>, fallback: u128) -> u128 {
    match value {
        Some(v) => v,
        None => fallback,
    }
}
#[unsafe(no_mangle)]
pub fn option128_after_one(prefix: u64, value: Option<u128>, suffix: u64) -> u128 {
    match value {
        Some(v) => v,
        None => prefix as u128,
    }
    .wrapping_add(suffix as u128)
}
#[unsafe(no_mangle)]
pub fn option128_after_five(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    match value {
        Some(v) => v,
        None => a as u128,
    }
    .wrapping_add(b as u128)
    .wrapping_add(c as u128)
    .wrapping_add(d as u128)
    .wrapping_add(e as u128)
    .wrapping_add(suffix as u128)
}
unsafe extern "Rust" {
    fn llvm_option128(prefix: u64, value: Option<u128>, fallback: u128) -> u128;
}
#[unsafe(no_mangle)]
pub extern "C" fn option128_call_llvm(
    value: u128,
    some: bool,
    prefix: u64,
    fallback: u128,
) -> u128 {
    let opt = if some { Some(value) } else { None };
    unsafe { llvm_option128(prefix, opt, fallback) }
}
