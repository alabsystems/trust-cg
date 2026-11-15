#![allow(improper_ctypes)]
use core::cell::UnsafeCell;
#[repr(C)]
pub struct Pair {
    a: u64,
    b: u64,
}
unsafe extern "C" {
    fn fixed_identity(a: &u64, b: &u64) -> bool;
    fn pair_identity(a: &Pair, b: &Pair) -> bool;
    fn ref_identity(a: &&u64, b: &&u64) -> bool;
    fn address(a: &u64) -> *const u64;
    fn cell_alias(a: &UnsafeCell<u64>, b: &UnsafeCell<u64>, x: u64) -> bool;
}
#[inline(never)]
fn rust_identity(a: &u64, b: &u64) -> bool {
    core::ptr::eq(a, b)
}
#[inline(never)]
fn rust_pair_identity(a: &Pair, b: &Pair) -> bool {
    core::ptr::eq(a, b)
}
#[inline(never)]
fn rust_address(a: &u64) -> *const u64 {
    a
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_same(a: u64) -> bool {
    let r = &a;
    unsafe { fixed_identity(r, r) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_same(a: u64) -> bool {
    let r = &a;
    rust_identity(r, r)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_alias(a: u64) -> bool {
    let r = &a;
    let s = &*r;
    unsafe { fixed_identity(r, s) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_alias(a: u64) -> bool {
    let r = &a;
    let s = &*r;
    rust_identity(r, s)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_branch(a: u64, b: u64, pick: bool) -> bool {
    let r = if pick { &a } else { &b };
    let s = if pick { &a } else { &b };
    unsafe { fixed_identity(r, s) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_branch(a: u64, b: u64, pick: bool) -> bool {
    let r = if pick { &a } else { &b };
    let s = if pick { &a } else { &b };
    rust_identity(r, s)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_projected(a: u64, b: u64) -> bool {
    let p = Pair { a, b };
    let r = &p.b;
    let s = &p.b;
    unsafe { fixed_identity(r, s) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_projected(a: u64, b: u64) -> bool {
    let p = Pair { a, b };
    let r = &p.b;
    let s = &p.b;
    rust_identity(r, s)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_pair(a: u64, b: u64) -> bool {
    let p = Pair { a, b };
    let r = &p;
    let s = &p;
    unsafe { pair_identity(r, s) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_pair(a: u64, b: u64) -> bool {
    let p = Pair { a, b };
    let r = &p;
    let s = &p;
    rust_pair_identity(r, s)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_across(a: u64) -> bool {
    let r = &a;
    let one = unsafe { address(r) };
    one == unsafe { address(r) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_across(a: u64) -> bool {
    let r = &a;
    let one = rust_address(r);
    one == rust_address(r)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_indirect(a: u64, f: unsafe extern "C" fn(&u64, &u64) -> bool) -> bool {
    let r = &a;
    unsafe { f(r, r) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_nested(a: u64) -> bool {
    let r = &a;
    let rr = &r;
    unsafe { ref_identity(rr, rr) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_cell(a: u64, b: u64) -> bool {
    let x = UnsafeCell::new(a);
    let r = &x;
    let s = &x;
    let same = unsafe { cell_alias(r, s, b) };
    same && unsafe { *x.get() } == b
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn c_distinct(a: u64) -> bool {
    let b = a;
    unsafe { !fixed_identity(&a, &b) }
}
#[unsafe(no_mangle)]
pub extern "C" fn rust_distinct(a: u64) -> bool {
    let b = a;
    !rust_identity(&a, &b)
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(i8)]
enum Signed {
    A = -111,
    B = 7,
    C = 115,
}
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
enum Unsigned {
    A = 0,
    B = 0x80000000,
    C = 0xffffffff,
}
fn signed(x: u8) -> Signed {
    match x % 3 {
        0 => Signed::A,
        1 => Signed::B,
        _ => Signed::C,
    }
}
fn unsigned(x: u8) -> Unsigned {
    match x % 3 {
        0 => Unsigned::A,
        1 => Unsigned::B,
        _ => Unsigned::C,
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn compare_signed(x: u8, y: u8) -> i8 {
    signed(x).cmp(&signed(y)) as i8
}
#[unsafe(no_mangle)]
pub extern "C" fn compare_unsigned(x: u8, y: u8) -> i8 {
    unsigned(x).cmp(&unsigned(y)) as i8
}

unsafe extern "C" {
    fn nested_shared(p: &&u64) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared_reborrow(p: &mut u64) -> u64 {
    let r = &*p;
    unsafe { nested_shared(&r) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_reborrow(p: *const u64) -> u64 {
    let r = unsafe { &*p };
    unsafe { nested_shared(&r) }
}

#[repr(C)]
pub struct Cursor {
    p: *const u64,
}
#[repr(C)]
pub struct RefCursor<'a> {
    p: &'a u64,
}
unsafe extern "C" {
    fn observe_raw(p: &Cursor) -> u64;
    fn observe_ref(p: &RefCursor<'_>) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_field(a: *const u64, b: *const u64) -> u64 {
    let mut c = Cursor { p: a };
    let x = unsafe { observe_raw(&c) };
    c.p = b;
    x.wrapping_add(unsafe { observe_raw(&c) })
        .wrapping_add(unsafe { *c.p })
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ref_field(a: &u64, b: &u64) -> u64 {
    let mut c = RefCursor { p: a };
    let x = unsafe { observe_ref(&c) };
    c.p = b;
    x.wrapping_add(unsafe { observe_ref(&c) })
        .wrapping_add(*c.p)
}

#[repr(transparent)]
struct ScalarWrapper(u64);
unsafe extern "C" {
    fn scalar_read(p: &u64) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn field_borrow(a: u64) -> bool {
    let n = ScalarWrapper(a);
    unsafe { fixed_identity(&n.0, &n.0) && scalar_read(&n.0) == a }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nested_field_borrow(a: u64) -> u64 {
    let n = ScalarWrapper(a);
    let r = &n.0;
    unsafe { nested_shared(&r) }
}
