#![no_std]
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
unsafe extern "Rust" {
    fn term_step(v: u64) -> u64;
    fn term_callback() -> fn(u64) -> u64;
    fn term_union_callback() -> fn(u64) -> core::mem::MaybeUninit<u64>;
    fn term_mut(v: &mut u64) -> u64;
    fn term_pair(v: u64) -> (u64, u64);
    fn term_words(v: u64) -> Words;
    fn term_union(v: u64) -> core::mem::MaybeUninit<u64>;
    fn term_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64;
}
#[unsafe(no_mangle)]
pub extern "C" fn term_scalar(v: u64) -> u64 {
    unsafe { term_step(v) }
}
#[unsafe(no_mangle)]
pub extern "C" fn term_alias(v: u64) -> u64 {
    let mut cell = v;
    cell = unsafe { term_mut(&mut cell) };
    cell
}
#[unsafe(no_mangle)]
pub extern "C" fn term_pair_result(v: u64) -> u64 {
    let pair = unsafe { term_pair(v) };
    pair.0 ^ pair.1
}
#[unsafe(no_mangle)]
pub extern "C" fn term_words_result(v: u64) -> u64 {
    let words = unsafe { term_words(v) };
    words.a ^ words.b ^ words.c ^ words.d
}
#[unsafe(no_mangle)]
pub extern "C" fn term_closure_scalar(v: u64) -> u64 {
    let mut cell = v;
    let mut f = || {
        cell = unsafe { term_step(cell) };
        cell
    };
    f()
}
#[unsafe(no_mangle)]
pub extern "C" fn term_closure_pair(v: u64) -> u64 {
    let f = |x| unsafe { term_pair(x) };
    let pair = f(v);
    pair.0 ^ pair.1
}
#[unsafe(no_mangle)]
pub extern "C" fn term_closure_words(v: u64) -> u64 {
    let f = |x| unsafe { term_words(x) };
    let words = f(v);
    words.a ^ words.b ^ words.c ^ words.d
}
struct Guard(u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            term_step(self.0);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn term_drop(v: u64) -> u64 {
    let guard = Guard(v);
    drop(guard);
    v
}
#[unsafe(no_mangle)]
pub extern "C" fn term_iter(v: u64) -> u64 {
    (0..4u64)
        .map(|i| unsafe { term_step(v.wrapping_add(i)) })
        .fold(0, u64::wrapping_add)
}

#[unsafe(no_mangle)]
pub extern "C" fn term_double_panic(v: u64) -> u64 {
    let _guard = Guard(v.wrapping_add(1));
    unsafe { term_step(v) }
}

#[unsafe(no_mangle)]
pub extern "C" fn term_union_result(v: u64) -> u64 {
    let mut storage = unsafe { term_union(v) };
    unsafe { term_read_union(&mut storage) }
}

#[unsafe(no_mangle)]
pub extern "C" fn term_indirect(v: u64) -> u64 {
    let callback = unsafe { term_callback() };
    callback(v)
}
#[unsafe(no_mangle)]
pub extern "C" fn term_indirect_union(v: u64) -> u64 {
    let callback = unsafe { term_union_callback() };
    let mut storage = callback(v);
    unsafe { term_read_union(&mut storage) }
}
struct IndirectGuard(fn(u64) -> u64, u64);
impl Drop for IndirectGuard {
    #[inline(never)]
    fn drop(&mut self) {
        (self.0)(self.1);
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn term_indirect_double_panic(v: u64) -> u64 {
    let callback = unsafe { term_callback() };
    let _guard = IndirectGuard(callback, v.wrapping_add(1));
    callback(v)
}
