#![no_std]
#[unsafe(no_mangle)]
pub fn tail_word(words: &[u64]) -> u64 {
    match words {
        [.., last] => *last,
        _ => 0,
    }
}
#[unsafe(no_mangle)]
pub fn end_words(words: &[u64]) -> u64 {
    match words {
        [first, .., last] => *first ^ *last,
        _ => 0,
    }
}
#[unsafe(no_mangle)]
pub fn tail_mut(words: &mut [u64], mask: u64) -> u64 {
    match words {
        [.., last] => {
            *last ^= mask;
            *last
        }
        _ => 0,
    }
}

#[repr(transparent)]
pub struct Bytes([u8]);
#[unsafe(no_mangle)]
pub fn tail_wrapped(bytes: &Bytes) -> u8 {
    match &bytes.0 {
        [.., last] => *last,
        _ => 0,
    }
}
#[unsafe(no_mangle)]
pub fn trim_wrapped(bytes: &Bytes) -> usize {
    let mut data = &bytes.0;
    while let Some((last, init)) = data.split_last()
        && *last == b'/'
    {
        data = init;
    }
    data.len()
}

#[repr(C)]
pub struct Head<T: ?Sized> {
    pub marker: u64,
    pub tail: T,
}
#[repr(C)]
pub struct Outer<T: ?Sized> {
    pub marker: u64,
    pub inner: Head<T>,
}
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
#[unsafe(no_mangle)]
pub fn last_u64(data: &Head<[u64]>) -> u64 {
    match &data.tail {
        [.., last] => *last,
        _ => data.marker,
    }
}
#[unsafe(no_mangle)]
pub fn last_two(data: &Head<[u16]>) -> u64 {
    match &data.tail {
        [.., a, b] => *a as u64 * 65536 + *b as u64,
        _ => data.marker,
    }
}
#[unsafe(no_mangle)]
pub fn mutate_last(data: &mut Head<[u64]>, mask: u64) -> u64 {
    match &mut data.tail {
        [.., last] => {
            let old = *last;
            *last ^= mask;
            old
        }
        _ => data.marker,
    }
}
#[unsafe(no_mangle)]
pub fn raw_read(data: *const Head<[u64]>) -> u64 {
    unsafe {
        match &(*data).tail {
            [.., last] => *last,
            _ => (*data).marker,
        }
    }
}
#[unsafe(no_mangle)]
pub fn raw_write(data: *mut Head<[u64]>, mask: u64) -> u64 {
    unsafe {
        match &mut (*data).tail {
            [.., last] => {
                let old = *last;
                *last ^= mask;
                old
            }
            _ => (*data).marker,
        }
    }
}
#[unsafe(no_mangle)]
pub fn nested_last(data: &Outer<[u64]>) -> u64 {
    match &data.inner.tail {
        [.., last] => *last,
        _ => data.inner.marker,
    }
}
#[unsafe(no_mangle)]
pub fn borrow_last(data: &Head<[u64]>) -> &u64 {
    match &data.tail {
        [.., last] => last,
        _ => &data.marker,
    }
}
#[unsafe(no_mangle)]
pub fn pointer_last(data: &Head<[u64]>) -> *const u64 {
    match &data.tail {
        [.., last] => last,
        _ => &data.marker,
    }
}
#[unsafe(no_mangle)]
pub fn pair_last(data: &Head<[Pair]>) -> *const Pair {
    match &data.tail {
        [.., last] => last,
        _ => core::ptr::null(),
    }
}
