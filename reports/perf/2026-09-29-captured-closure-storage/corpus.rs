#![no_std]
#[inline(never)]
fn apply<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 { f(x) }
#[inline(never)]
fn nested<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    let g = |v| f(v);
    apply(g, x)
}
#[inline(never)]
fn forwarded<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    nested(|v| f(v), x)
}
#[unsafe(no_mangle)]
pub extern "C" fn closure_hash(seed: u64, x: u32) -> u64 {
    let mut value = seed;
    forwarded(|v| { value = value.wrapping_mul(31).wrapping_add(v as u64); value }, x)
}
