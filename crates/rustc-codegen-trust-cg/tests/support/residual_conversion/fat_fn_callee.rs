#![no_std]
// The closure bodies are compiled here and reached only through their `&dyn
// Fn` vtable from `invoke_dynamic`, which another (LLVM) crate compiles: six
// `u64`s, a `&[u64]` whose two lanes straddle x7 and the stack, then a `u64`
// on the stack.
unsafe extern "Rust" {
    fn invoke_dynamic(
        op: &dyn Fn(u64, u64, u64, u64, u64, u64, &[u64], u64) -> u64,
        data: &[u64],
        seed: u64,
    ) -> u64;
}
#[unsafe(no_mangle)]
pub fn cg_fat_closure(data: &[u64], seed: u64) -> u64 {
    let closure =
        |a, b, c, d, e, f, s: &[u64], g| a + b + c + d + e + f + g + s.len() as u64 + s[0];
    unsafe { invoke_dynamic(&closure, data, seed) }
}
// The same crossing with a result that depends on every argument's position.
#[unsafe(no_mangle)]
pub fn cg_fat_closure_ordered(data: &[u64], seed: u64) -> u64 {
    let closure = |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u64], g: u64| {
        a ^ b.rotate_left(7)
            ^ c.rotate_left(13)
            ^ d.rotate_left(19)
            ^ e.rotate_left(29)
            ^ f.rotate_left(37)
            ^ g.rotate_left(43)
            ^ (s.len() as u64).rotate_left(51)
            ^ s[s.len() - 1].rotate_left(57)
    };
    unsafe { invoke_dynamic(&closure, data, seed) }
}
