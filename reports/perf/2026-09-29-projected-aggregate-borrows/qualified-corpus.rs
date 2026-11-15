#![no_std]

use core::{marker::PhantomData, ptr::NonNull};

struct Cursor<'a> {
    next: NonNull<u8>,
    end: *const u8,
    marker: PhantomData<&'a u8>,
}
struct Wrapper<'a> {
    cursor: Cursor<'a>,
}
#[repr(C)]
struct Outer<'a> {
    before: u64,
    wrapper: Wrapper<'a>,
    after: u64,
}

#[inline(never)]
unsafe fn advance(cursor: &mut Cursor<'_>) -> u64 {
    let value = unsafe { *cursor.next.as_ptr() };
    cursor.next = unsafe { NonNull::new_unchecked(cursor.next.as_ptr().add(1)) };
    value as u64
}

#[inline(never)]
unsafe fn peek(cursor: &Cursor<'_>) -> u64 {
    unsafe { *cursor.next.as_ptr() as u64 }
}

#[inline(never)]
unsafe fn finish(wrapper: Wrapper<'_>, first: u64) -> u64 {
    first
        | ((unsafe { *wrapper.cursor.next.as_ptr() } as u64) << 8)
        | (((wrapper.cursor.end as usize).wrapping_sub(wrapper.cursor.next.as_ptr() as usize)
            as u64)
            << 16)
}

#[inline(never)]
unsafe fn finish_outer(outer: Outer<'_>, first: u64) -> u64 {
    (unsafe { finish(outer.wrapper, first) }) ^ outer.before ^ outer.after
}

// Keep construction in the exported body: a call result would independently
// force a slot and hide the projected-borrow regression.
macro_rules! wrapper {
    ($data:expr, $len:expr) => {
        Wrapper {
            cursor: Cursor {
                next: unsafe { NonNull::new_unchecked($data as *mut u8) },
                end: unsafe { $data.add($len) },
                marker: PhantomData,
            },
        }
    };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn projected_cursor(data: *const u8, len: usize) -> u64 {
    let mut wrapper = wrapper!(data, len);
    let first = unsafe { advance(&mut wrapper.cursor) };
    unsafe { finish(wrapper, first) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared_cursor(data: *const u8, len: usize) -> u64 {
    let wrapper = wrapper!(data, len);
    let first = unsafe { peek(&wrapper.cursor) };
    unsafe { finish(wrapper, first) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn nested_cursor(data: *const u8, len: usize, seed: u64) -> u64 {
    let mut outer = Outer {
        before: seed,
        wrapper: wrapper!(data, len),
        after: seed.rotate_left(17),
    };
    let first = unsafe { advance(&mut outer.wrapper.cursor) };
    unsafe { finish_outer(outer, first) }
}

// repr(Rust) places the wide field before the byte. Both the callee and the
// whole-value move must observe physical offsets rather than declaration order.
struct Pair {
    byte: u32,
    wide: u64,
    tail: u32,
}
struct PairWrapper {
    pair: Pair,
}
#[inline(never)]
fn mutate_pair(pair: &mut Pair) {
    pair.byte = pair.byte.wrapping_add(37) & 255;
    pair.wide = pair.wide.rotate_left(13) ^ 0xa758_60b1_5d9c_3e2f;
}
#[inline(never)]
fn consume_pair(wrapper: PairWrapper) -> u64 {
    wrapper.pair.wide
        ^ (wrapper.pair.byte as u64).wrapping_mul(0x0101_0101_0101_0101)
        ^ ((wrapper.pair.tail as u64) << 32)
}
#[unsafe(no_mangle)]
pub extern "C" fn reordered_pair(byte: u8, wide: u64) -> u64 {
    let mut wrapper = PairWrapper {
        pair: Pair {
            byte: byte as u32,
            wide,
            tail: 0xdead_beef,
        },
    };
    mutate_pair(&mut wrapper.pair);
    consume_pair(wrapper)
}
