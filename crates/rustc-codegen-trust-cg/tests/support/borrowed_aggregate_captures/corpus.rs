#![no_std]

#[inline(never)]
fn invoke<F: FnMut(u32) -> u16>(mut f: F, value: u32) -> u16 {
    let first = f(value);
    first ^ f(value.rotate_left(7))
}

// The local array's address is stored in the Option::map closure environment.
// Both the closure result and subsequent direct reads must see its writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_map(value: u32, present: bool, out: *mut u16) -> u16 {
    let mut buf = [0x1357u16, 0x2468];
    let mut extra = 0xaaaa;
    let option = if present { Some(value) } else { None };
    let result = option.map(|c| {
        buf[0] = c as u16;
        buf[1] = (c >> 16) as u16;
        extra = buf[1];
        buf[0]
    });
    unsafe {
        *out = buf[0];
        *out.add(1) = buf[1];
        *out.add(2) = extra;
    }
    result.unwrap_or(0xbbbb)
}

// A move capture of a branch-selected reference, with intermediate reference
// copies, needs a stable address for every possible referent.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn selected_array(value: u32, choose: bool, out: *mut u16) -> u16 {
    let mut a = [0x1122u16, 0x3344];
    let mut b = [0x5566u16, 0x7788];
    let selected = if choose { &mut a } else { &mut b };
    let copied = selected;
    let result = invoke(
        move |v| {
            copied[0] = copied[0].wrapping_add(v as u16);
            copied[1] ^= (v >> 16) as u16;
            copied[0] ^ copied[1]
        },
        value,
    );
    unsafe {
        *out = a[0];
        *out.add(1) = a[1];
        *out.add(2) = b[0];
        *out.add(3) = b[1];
    }
    result
}

#[repr(C)]
struct Pair {
    left: u64,
    right: u64,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn aggregate_capture(value: u32, out: *mut u64) -> u16 {
    let mut pair = Pair {
        left: 0x123456789abcdef0,
        right: 0xfedcba9876543210,
    };
    let mut other = Pair {
        left: 0xfffffffffffffff0,
        right: 0x0102030405060708,
    };
    let mut tuple = (0x1234u16, 0x5678u16);
    let shared = [0x1020304050607080u64, value as u64, 0x8877665544332211];
    // Unlike arrays, these flat structs get slots only when the captured
    // reference's possible referents are followed through the join and copy.
    let selected = if value & 1 == 0 {
        &mut pair
    } else {
        &mut other
    };
    let p = selected;
    let t = &mut tuple;
    let r = &shared;
    let copied = r;
    let result = invoke(
        move |v| {
            p.left = p.left.wrapping_add(v as u64);
            p.right ^= copied[0] ^ copied[1] ^ copied[2];
            t.0 = t.0.wrapping_add(v as u16);
            t.1 ^= (v >> 16) as u16;
            (p.left ^ p.right) as u16 ^ t.0 ^ t.1
        },
        value,
    );
    unsafe {
        *out = pair.left;
        *out.add(1) = pair.right;
        *out.add(2) = tuple.0 as u64;
        *out.add(3) = tuple.1 as u64;
        *out.add(4) = shared[0];
        *out.add(5) = shared[1];
        *out.add(6) = shared[2];
        *out.add(7) = other.left;
        *out.add(8) = other.right;
    }
    result
}
