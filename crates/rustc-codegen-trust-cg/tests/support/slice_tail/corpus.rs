#![no_std]
#![feature(ptr_metadata)]

#[repr(C)]
pub struct Header<T: ?Sized> {
    pub tag: u64,
    pub count: u64,
    pub data: T,
}
#[repr(C, align(16))]
pub struct Nested<T: ?Sized> {
    pub prefix: u64,
    pub inner: Header<T>,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn unsize_header(p: &mut Header<[u64; 4]>) -> &mut Header<[u64]> {
    p
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn unsize_nested(p: &mut Nested<[u64; 4]>) -> &mut Nested<[u64]> {
    p
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn identity(p: &mut Header<[u64]>) -> &mut Header<[u64]> {
    p
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn header_read(p: &Header<[u64]>) -> u64 {
    p.tag.wrapping_add(p.count)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn tail(p: &Header<[u64]>) -> &[u64] {
    &p.data
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn tail_mut(p: &mut Header<[u64]>) -> &mut [u64] {
    &mut p.data
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn nested_tail(p: &Nested<[u64]>) -> &[u64] {
    &p.inner.data
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn header_field(p: &mut Header<[u64]>) -> &mut u64 {
    &mut p.count
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn nested_inner(p: &mut Nested<[u64]>) -> &mut Header<[u64]> {
    &mut p.inner
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn metadata(p: *mut Header<[u64]>) -> usize {
    core::ptr::metadata(p)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn size(p: &Nested<[u64]>) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn align(p: &Nested<[u64]>) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn update(p: &mut Header<[u64]>, salt: u64) -> u64 {
    p.tag = p.tag.wrapping_add(salt);
    p.count ^= salt;
    let mut sum = p.tag.wrapping_add(p.count);
    for value in &mut p.data {
        *value = value.wrapping_add(salt);
        sum = sum.wrapping_add(*value);
    }
    sum
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn exercise(
    p: *mut Nested<[u64; 4]>,
    len: usize,
    salt: u64,
    mode: u32,
) -> u64 {
    let raw: *mut Nested<[u64]> = core::ptr::from_raw_parts_mut(p.cast::<()>(), len);
    let value = unsafe { &mut *raw };
    match mode {
        0 => header_read(&value.inner),
        1 => metadata(&mut value.inner) as u64,
        2 => size(value) as u64,
        3 => align(value) as u64,
        4 => tail(identity(nested_inner(value)))
            .iter()
            .copied()
            .fold(0u64, u64::wrapping_add),
        5 => {
            *header_field(&mut value.inner) ^= salt;
            value.inner.count
        }
        6 => update(&mut value.inner, salt),
        7 => nested_tail(value).len() as u64,
        8 => {
            let s = tail_mut(&mut value.inner);
            if len != 0 {
                s[len - 1] ^= salt;
                s[len - 1]
            } else {
                salt
            }
        }
        9 => core::mem::size_of_val(unsize_nested(unsafe { &mut *p })) as u64,
        10 => metadata(unsize_header(unsafe { &mut (*p).inner })) as u64,
        11 => tail(&value.inner)
            .iter()
            .copied()
            .fold(salt, u64::wrapping_sub),
        12 => {
            let mut acc = salt;
            for _ in 0..3 {
                acc = tail(&value.inner)
                    .iter()
                    .copied()
                    .fold(acc, u64::wrapping_sub);
            }
            acc
        }
        13 => tail(&value.inner).iter().copied().fold(salt, |acc, item| {
            acc.wrapping_mul(3).wrapping_add(item ^ salt)
        }),
        _ => u64::MAX,
    }
}

#[repr(C)]
pub struct Small<T: ?Sized> {
    pub marker: u8,
    pub data: T,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn shape_probe(raw: *mut u8, len: usize, kind: u32) -> u64 {
    let (size, align, length, last) = match kind {
        0 => {
            let p: *mut Small<[u8]> = core::ptr::from_raw_parts_mut(raw.cast::<()>(), len);
            let p = unsafe { &mut *p };
            if len != 0 {
                p.data[len - 1] = p.data[len - 1].wrapping_add(p.marker);
            }
            (
                core::mem::size_of_val(p),
                core::mem::align_of_val(p),
                p.data.len(),
                if len != 0 { p.data[len - 1] as u64 } else { 0 },
            )
        }
        1 => {
            let p: *mut Small<[u32]> = core::ptr::from_raw_parts_mut(raw.cast::<()>(), len);
            let p = unsafe { &mut *p };
            if len != 0 {
                p.data[len - 1] = p.data[len - 1].wrapping_add(p.marker as u32);
            }
            (
                core::mem::size_of_val(p),
                core::mem::align_of_val(p),
                p.data.len(),
                if len != 0 {
                    (p.data[len - 1] & 255) as u64
                } else {
                    0
                },
            )
        }
        2 => {
            let p: *const Small<[()]> = core::ptr::from_raw_parts(raw.cast::<()>(), len);
            let p = unsafe { &*p };
            (
                core::mem::size_of_val(p),
                core::mem::align_of_val(p),
                p.data.len(),
                0,
            )
        }
        _ => {
            let p: *const Small<str> = core::ptr::from_raw_parts(raw.cast::<()>(), len);
            let p = unsafe { &*p };
            let bytes = p.data.as_bytes();
            (
                core::mem::size_of_val(p),
                core::mem::align_of_val(p),
                bytes.len(),
                if len != 0 { bytes[len - 1] as u64 } else { 0 },
            )
        }
    };
    ((size as u64) << 32) | ((align as u64) << 16) | (last << 8) | length as u64
}
