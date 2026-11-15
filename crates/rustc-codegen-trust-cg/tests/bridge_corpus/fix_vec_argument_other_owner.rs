// These upstream functions receive a Vec but are not methods owned by Vec.
use std::ptr::NonNull;

#[inline(never)]
fn inherent(values: &mut Vec<u8>) -> NonNull<Vec<u8>> {
    NonNull::from_mut(values)
}

#[inline(never)]
fn trait_method(values: &mut Vec<u8>) -> NonNull<Vec<u8>> {
    NonNull::from(values)
}

#[inline(never)]
fn free_function(values: &mut Vec<u8>) -> *mut Vec<u8> {
    std::ptr::from_mut(values)
}

fn main() {
    let mut values = Vec::with_capacity(16);
    values.extend_from_slice(b"hello");
    let address = &mut values as *mut Vec<u8>;
    let mut a = inherent(&mut values);
    if a.as_ptr() != address {
        std::process::exit(74);
    }
    unsafe { a.as_mut().push(b'!') };
    let mut b = trait_method(&mut values);
    if b.as_ptr() != address {
        std::process::exit(74);
    }
    unsafe { b.as_mut().push(b'?') };
    let c = free_function(&mut values);
    if c != address {
        std::process::exit(74);
    }
    unsafe { (*c).push(b'.') };
    if values.len() != 8 || values[5] != b'!' || values[6] != b'?' || values[7] != b'.' {
        std::process::exit(75);
    }
    // Explicit upstream impls on &Vec and &mut Vec remain genuine receivers.
    let mut sum = 0u64;
    for value in &values {
        sum += u64::from(*value);
    }
    if sum != 674 {
        std::process::exit(76);
    }
    for value in &mut values {
        *value = value.wrapping_add(1);
    }
    if values[0] != b'i' || values[7] != b'/' {
        std::process::exit(77);
    }
    drop(values);
}
