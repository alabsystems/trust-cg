#![no_std]
#![feature(titlecase)]
extern crate alloc;
use alloc::{string::String, vec::Vec};
use core::alloc::{GlobalAlloc, Layout};

unsafe extern "C" {
    fn test_alloc(size: usize, align: usize) -> *mut u8;
    fn test_free(ptr: *mut u8);
    fn abort() -> !;
}
struct Heap;
unsafe impl GlobalAlloc for Heap {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { test_alloc(layout.size(), layout.align()) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, _: Layout) {
        unsafe { test_free(ptr) }
    }
}
#[global_allocator]
static HEAP: Heap = Heap;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    unsafe { abort() }
}

fn hash(bytes: &[u8]) -> u64 {
    let mut out = 0x1978u64;
    let mut i = 0;
    while i < bytes.len() {
        out = out.wrapping_mul(37).wrapping_add(bytes[i] as u64);
        i += 1;
    }
    out ^ (bytes.len() as u64).rotate_left(17)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_utf16(data: *const u8, len: usize, kind: u32) -> u64 {
    let data = unsafe { core::slice::from_raw_parts(data, len) };
    let value = match kind {
        0 => String::from_utf16be(data),
        1 => String::from_utf16le(data),
        2 => Ok(String::from_utf16be_lossy(data)),
        _ => Ok(String::from_utf16le_lossy(data)),
    };
    match value {
        Ok(s) => hash(s.as_bytes()),
        Err(_) => 0xfedcba9876543210,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_unicode(data: *const u8, len: usize, kind: u32) -> u64 {
    let s = unsafe { core::str::from_utf8_unchecked(core::slice::from_raw_parts(data, len)) };
    let value = match kind {
        0 => s.to_lowercase(),
        1 => s.to_uppercase(),
        _ => s.word_to_titlecase(),
    };
    hash(value.as_bytes())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_vec_drain(
    data: *const u8,
    len: usize,
    start: usize,
    end: usize,
    take: usize,
) -> u64 {
    let data = unsafe { core::slice::from_raw_parts(data, len) };
    let mut values = Vec::new();
    values.extend_from_slice(data);
    let mut out = 1u64;
    {
        let mut drain = values.drain(start..end);
        let mut i = 0;
        while i < take {
            match drain.next() {
                Some(v) => out = out.wrapping_mul(17).wrapping_add(v as u64),
                None => break,
            }
            i += 1;
        }
    }
    out ^ hash(&values)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_string_drain(
    data: *const u8,
    len: usize,
    start: usize,
    end: usize,
    take: usize,
    state: *mut usize,
) -> u64 {
    let data = unsafe { core::str::from_utf8_unchecked(core::slice::from_raw_parts(data, len)) };
    let mut value = String::from(data);
    let mut out = 1u64;
    {
        let mut drain = value.drain(start..end);
        let mut i = 0;
        while i < take {
            match drain.next() {
                Some(c) => out = out.wrapping_mul(17).wrapping_add(c as u64),
                None => break,
            }
            i += 1;
        }
        let (low, high) = drain.size_hint();
        unsafe {
            *state = low;
            *state.add(1) = high.unwrap_or(usize::MAX);
            *state.add(2) = drain.as_str().len();
            *state.add(3) = hash(drain.as_str().as_bytes()) as usize;
        }
    }
    out ^ hash(value.as_bytes())
}
