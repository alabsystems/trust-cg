#[inline(never)]
fn rev<'a>(v: &mut [&'a u32]) {
    v.reverse();
}
#[inline(never)]
fn sw(a: &mut *const u32, b: &mut *const u32) {
    core::mem::swap(a, b);
}
#[no_mangle]
pub extern "C" fn cap_swap(a: u32, b: u32) -> u32 {
    let (x, y, z) = (a, b, a ^ b);
    let mut v = [&x, &y, &z];
    rev(&mut v);
    let mut p: *const u32 = &x;
    let mut q: *const u32 = &y;
    sw(&mut p, &mut q);
    unsafe { *v[0] ^ *p ^ (*q).rotate_left(3) }
}
