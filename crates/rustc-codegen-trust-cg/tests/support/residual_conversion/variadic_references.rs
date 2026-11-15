use core::cell::UnsafeCell;
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
unsafe extern "C" {
    fn ref_shared(tag: u32, ...) -> u64;
    fn ref_write(tag: u32, ...) -> u64;
    fn ref_pair(tag: u32, ...) -> u64;
    fn ref_cell(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared(a: i32) -> u64 {
    unsafe { ref_shared(17, &a) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn promoted() -> u64 {
    unsafe { ref_shared(17, &-19i32) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn mutate(a: u64, b: u64) -> u64 {
    let mut x = a;
    let r = unsafe { ref_write(23, &mut x, b) };
    x ^ r
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn forward(p: &mut u64, b: u64) -> u64 {
    let r = unsafe { ref_write(23, &mut *p, b) };
    *p ^ r
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pair_local(a: u64, b: u64, x: u64) -> u64 {
    let mut p = Pair { a, b };
    let r = unsafe { ref_pair(31, &mut p, x) };
    p.a ^ p.b ^ r
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pair_forward(p: &mut Pair, x: u64) -> u64 {
    let r = unsafe { ref_pair(31, &mut *p, x) };
    p.a ^ p.b ^ r
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn cell(a: u64, b: u64) -> u64 {
    let p = UnsafeCell::new(a);
    let r = unsafe { ref_cell(37, &p, b) };
    (unsafe { *p.get() }) ^ r
}

unsafe extern "C" {
    fn ref_many(count: u32, ...) -> u64;
    fn ref_identity(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn identity(a: u64) -> u64 {
    let r = &a;
    unsafe { ref_identity(0, r, r) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn many(a: u64) -> u64 {
    let mut a0 = a.wrapping_add(0);
    let mut a1 = a.wrapping_add(1);
    let mut a2 = a.wrapping_add(2);
    let mut a3 = a.wrapping_add(3);
    let mut a4 = a.wrapping_add(4);
    let mut a5 = a.wrapping_add(5);
    let mut a6 = a.wrapping_add(6);
    let mut a7 = a.wrapping_add(7);
    let mut a8 = a.wrapping_add(8);
    let mut a9 = a.wrapping_add(9);
    unsafe {
        ref_many(
            10, &mut a0, &mut a1, &mut a2, &mut a3, &mut a4, &mut a5, &mut a6, &mut a7, &mut a8,
            &mut a9,
        )
    };
    let mut r = 31u64;
    r = (r ^ a0).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a1).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a2).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a3).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a4).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a5).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a6).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a7).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a8).wrapping_mul(0x9e3779b97f4a7c15);
    r = (r ^ a9).wrapping_mul(0x9e3779b97f4a7c15);
    r
}

unsafe extern "C" {
    fn ref_pair_identity(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn identity_pair(a: u64, b: u64) -> u64 {
    let value = Pair { a, b };
    let r = &value;
    unsafe { ref_pair_identity(0, r, r) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn identity_projected(a: u64, b: u64) -> u64 {
    let value = Pair { a, b };
    let r = &value.b;
    unsafe { ref_identity(0, r, r) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn identity_branch(a: u64, b: u64, choose: bool) -> u64 {
    let r = if choose { &a } else { &b };
    let q = &*r;
    unsafe { ref_identity(0, r, q) }
}
