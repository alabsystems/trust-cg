#![no_std]
use borrowed_slice_types::*;
#[unsafe(no_mangle)]
pub fn byte_first(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8 {
    match v {
        (true, ([], _, [a, ..])) => a as *const u8,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn byte_second(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8 {
    match v {
        (true, ([], _, [_, a, ..])) => a as *const u8,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn byte_last(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8 {
    match v {
        (true, ([], _, [_, .., a])) => a as *const u8,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn byte_penultimate(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8 {
    match v {
        (true, ([], _, [.., a, _])) => a as *const u8,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn byte_single(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8 {
    match v {
        (true, ([], _, [a])) => a as *const u8,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn byte_runtime(v: (u64, (&[u8], &[u8])), index: usize) -> *const u8 {
    if index < v.1.1.len() {
        &v.1.1[index] as *const u8
    } else {
        core::ptr::null()
    }
}
#[unsafe(no_mangle)]
pub fn byte_mutable(v: (u64, (&mut [u8], u64))) -> *mut u8 {
    match v.1.0 {
        [_, .., last] => last as *mut u8,
        _ => core::ptr::null_mut(),
    }
}
#[unsafe(no_mangle)]
pub fn word_first(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64 {
    match v {
        (true, ([], _, [a, ..])) => a as *const u64,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn word_second(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64 {
    match v {
        (true, ([], _, [_, a, ..])) => a as *const u64,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn word_last(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64 {
    match v {
        (true, ([], _, [_, .., a])) => a as *const u64,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn word_penultimate(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64 {
    match v {
        (true, ([], _, [.., a, _])) => a as *const u64,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn word_single(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64 {
    match v {
        (true, ([], _, [a])) => a as *const u64,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn word_runtime(v: (u64, (&[u64], &[u64])), index: usize) -> *const u64 {
    if index < v.1.1.len() {
        &v.1.1[index] as *const u64
    } else {
        core::ptr::null()
    }
}
#[unsafe(no_mangle)]
pub fn word_mutable(v: (u64, (&mut [u64], u64))) -> *mut u64 {
    match v.1.0 {
        [_, .., last] => last as *mut u64,
        _ => core::ptr::null_mut(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_first(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide {
    match v {
        (true, ([], _, [a, ..])) => a as *const Wide,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_second(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide {
    match v {
        (true, ([], _, [_, a, ..])) => a as *const Wide,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_last(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide {
    match v {
        (true, ([], _, [_, .., a])) => a as *const Wide,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_penultimate(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide {
    match v {
        (true, ([], _, [.., a, _])) => a as *const Wide,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_single(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide {
    match v {
        (true, ([], _, [a])) => a as *const Wide,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn wide_runtime(v: (u64, (&[Wide], &[Wide])), index: usize) -> *const Wide {
    if index < v.1.1.len() {
        &v.1.1[index] as *const Wide
    } else {
        core::ptr::null()
    }
}
#[unsafe(no_mangle)]
pub fn wide_mutable(v: (u64, (&mut [Wide], u64))) -> *mut Wide {
    match v.1.0 {
        [_, .., last] => last as *mut Wide,
        _ => core::ptr::null_mut(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_first(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero {
    match v {
        (true, ([], _, [a, ..])) => a as *const Zero,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_second(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero {
    match v {
        (true, ([], _, [_, a, ..])) => a as *const Zero,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_last(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero {
    match v {
        (true, ([], _, [_, .., a])) => a as *const Zero,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_penultimate(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero {
    match v {
        (true, ([], _, [.., a, _])) => a as *const Zero,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_single(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero {
    match v {
        (true, ([], _, [a])) => a as *const Zero,
        _ => core::ptr::null(),
    }
}
#[unsafe(no_mangle)]
pub fn zero_runtime(v: (u64, (&[Zero], &[Zero])), index: usize) -> *const Zero {
    if index < v.1.1.len() {
        &v.1.1[index] as *const Zero
    } else {
        core::ptr::null()
    }
}
#[unsafe(no_mangle)]
pub fn zero_mutable(v: (u64, (&mut [Zero], u64))) -> *mut Zero {
    match v.1.0 {
        [_, .., last] => last as *mut Zero,
        _ => core::ptr::null_mut(),
    }
}
#[unsafe(no_mangle)]
pub fn mutate_words(v: (bool, (&mut [u64], u64)), value: u64) -> bool {
    match v {
        (true, ([first, .., last], _)) => {
            *last = value;
            *first ^= value;
            true
        }
        _ => false,
    }
}
#[unsafe(no_mangle)]
pub fn select_last<'a>(a: &'a [u64], b: &'a [u64], choose: bool) -> *const u64 {
    let s = if choose { a } else { b };
    match s {
        [.., last] => last as *const u64,
        _ => core::ptr::null(),
    }
}

#[unsafe(no_mangle)]
pub fn byte_middle(v: (u64, (&[u8], &[u8]))) -> (*const u8, usize) {
    match v.1.1 {
        [_, middle @ .., _] => (middle.as_ptr(), middle.len()),
        _ => (core::ptr::null(), 0),
    }
}

#[unsafe(no_mangle)]
pub fn word_middle(v: (u64, (&[u64], &[u64]))) -> (*const u64, usize) {
    match v.1.1 {
        [_, middle @ .., _] => (middle.as_ptr(), middle.len()),
        _ => (core::ptr::null(), 0),
    }
}

#[unsafe(no_mangle)]
pub fn wide_middle(v: (u64, (&[Wide], &[Wide]))) -> (*const Wide, usize) {
    match v.1.1 {
        [_, middle @ .., _] => (middle.as_ptr(), middle.len()),
        _ => (core::ptr::null(), 0),
    }
}

#[unsafe(no_mangle)]
pub fn zero_middle(v: (u64, (&[Zero], &[Zero]))) -> (*const Zero, usize) {
    match v.1.1 {
        [_, middle @ .., _] => (middle.as_ptr(), middle.len()),
        _ => (core::ptr::null(), 0),
    }
}
