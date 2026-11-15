#![no_std]
unsafe extern "Rust" {
    fn inspect_debug(value: &dyn core::fmt::Debug, tag: u64);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_array(a: &[u8; 4], tag: u64) {
    unsafe { inspect_debug(&a, tag) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_words(a: &[u64; 3], tag: u64) {
    unsafe { inspect_debug(&a, tag) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_empty(a: &[u8; 0], tag: u64) {
    unsafe { inspect_debug(&a, tag) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_slice(a: &[u8], tag: u64) {
    unsafe { inspect_debug(&a, tag) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_nested(a: &[u8; 4], tag: u64) {
    unsafe { inspect_debug(&&a, tag) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn assert_slice(expected: [u8; 4], actual: &[u8]) {
    assert_eq!(expected, actual);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn assert_arrays(expected: &[u64; 3], actual: &[u64; 3]) {
    assert_eq!(expected, actual);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn array_ref_identity(a: &[u8; 4]) -> bool {
    let r = &a;
    core::ptr::eq(*r, a)
}
unsafe extern "Rust" {
    fn inspect_debug_address(value: &dyn core::fmt::Debug, expected: *const (), tag: u64);
    fn report_drop(a: u64, b: u64);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn debug_address(a: &[u8; 4], tag: u64) {
    unsafe {
        inspect_debug_address(&a, (&a as *const &[u8; 4]).cast(), tag);
    }
}
trait Set {
    fn set(&mut self, n: u8);
}
impl Set for &mut [u8; 4] {
    #[inline(never)]
    fn set(&mut self, n: u8) {
        self[2] = n;
    }
}
#[inline(never)]
fn apply(a: &mut dyn Set, n: u8) {
    a.set(n);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn mutable_array(mut a: &mut [u8; 4], n: u8) {
    let r = &mut a;
    apply(r, n);
}
#[repr(C)]
struct Guard {
    a: u64,
    b: u64,
}
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { report_drop(self.a, self.b) }
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn assert_drop(a: [u8; 4], b: &[u8], tag: u64) {
    let _guard = Guard {
        a: tag,
        b: tag ^ 0xabcdef,
    };
    assert_eq!(a, b);
}
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn load16(p: *const [u8; 2]) -> u16 {
    unsafe { core::mem::transmute(*p) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn load32(p: *const [u8; 4]) -> u32 {
    unsafe { core::mem::transmute(*p) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn load64(p: *const [u8; 8]) -> u64 {
    unsafe { core::mem::transmute(*p) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn load128(p: *const [u8; 16]) -> u128 {
    unsafe { core::mem::transmute(*p) }
}
#[inline(never)]
fn replace_ref<'a>(slot: &mut &'a [u8; 4], other: &'a [u8; 4]) {
    *slot = other;
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn replaced_pointer<'a>(mut a: &'a [u8; 4], b: &'a [u8; 4]) -> u16 {
    let mut r = &mut a;
    replace_ref(&mut r, b);
    u16::from(a[0]) * 256 + u16::from(a[3])
}

#[derive(Debug)]
struct Holder<'a> {
    bytes: &'a [u8],
    word: u64,
}
#[inline(never)]
fn inspect_holder(h: &Holder<'_>) -> u64 {
    unsafe {
        inspect_debug(&h, h.word);
    }
    h.bytes.len() as u64 ^ h.word
}
#[unsafe(no_mangle)]
pub fn borrowed_holder(bytes: &[u8], tag: u64) -> u64 {
    inspect_holder(&Holder { bytes, word: tag })
}

#[derive(Clone, Copy, Debug)]
enum Choice {
    Empty,
    One(u64),
    Two(u64, u64),
}
#[inline(never)]
fn inspect_choice(a: &Choice, tag: u64) -> u64 {
    unsafe {
        inspect_debug(&a, tag);
    }
    let kind = match a {
        Choice::Empty => 1,
        Choice::One(_) => 2,
        Choice::Two(..) => 3,
    };
    let copied = *a;
    let value = match copied {
        Choice::Empty => 0,
        Choice::One(x) => x,
        Choice::Two(x, y) => x.wrapping_add(y),
    };
    value ^ kind
}
#[unsafe(no_mangle)]
pub fn borrowed_enum(x: u64, y: u64, tag: u64) -> u64 {
    let value = match tag % 3 {
        0 => Choice::Empty,
        1 => Choice::One(x),
        _ => Choice::Two(x, y),
    };
    inspect_choice(&value, tag)
}

#[repr(C)]
#[derive(Debug)]
pub struct Record {
    pub a: u64,
    pub b: u64,
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn stored_field(a: &mut Record, n: u64, tag: u64) -> u64 {
    unsafe {
        inspect_debug(&a, tag);
    }
    a.a = n;
    a.b
}
