#![no_std]
// Each read is `*(&raw const a as *const u64).add(i)` with `i < 8`. `a[i]`
// carries a bounds check, a source Assert this backend refuses before register
// allocation; `a.as_ptr()` goes through an unsized `&[u64]`, which the bridge
// lowers to a module `validate_module` rejects.
use core::hint::black_box;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub fn trustcg_split_copy_k_xsh_8(src: &[u64; 8]) -> u64 {
    let a = black_box(*src);
    let mut acc: u64 = 0; let mut t: u64 = 0;
    let mut i = 0usize;
    while i < 8 { let x = unsafe { *(&raw const a as *const u64).add(i) }; acc = acc.wrapping_add(x ^ (x >> 29) ^ (x << 7)); t = t.wrapping_add(i as u64 * 3 + 1); i += 1; }
    black_box(acc ^ t.wrapping_mul(5))
}
#[no_mangle]
pub fn trustcg_split_copy_k_mul_8(src: &[u64; 8]) -> u64 {
    let a = black_box(*src);
    let mut acc: u64 = 0; let mut t: u64 = 0;
    let mut i = 0usize;
    while i < 8 { let x = unsafe { *(&raw const a as *const u64).add(i) }; acc = acc.wrapping_add((x ^ (x >> 29)).wrapping_mul(0x2545_F491_4F6C_DD1D)); t = t.wrapping_add(i as u64 * 3 + 1); i += 1; }
    black_box(acc ^ t.wrapping_mul(5))
}
