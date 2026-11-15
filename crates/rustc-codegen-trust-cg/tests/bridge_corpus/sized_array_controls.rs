// CORPUS FIXTURE — the CONTROLS for the sized-array lane. Every shape here
// COMPILES AND MATCHES on the UNPATCHED backend too; the lane must not move any
// of them.
//
//  * `[T; 0]` — a zero-length array is a ZST and keeps its existing `Unit`
//    mapping (`rust_ty_to_trust_ir_ty`'s `len == 0` arm). Its unsize to `&[T]`
//    keeps a length of 0.
//  * a THIN `&[T; N]` reference to a SCALAR-element array — the scalar-field
//    flattening still represents it, so the widened arm must return `Ok(None)`
//    for it and leave its representation exactly as it was.
//  * a `&[T]` SLICE (fat `{data,len}`) — a different family, owned by another
//    lane. Indexing, `len`, and iteration through it must be untouched.
//  * a `&[[u8; 4]; N]` NESTED-array pointee — one of the three shape triggers
//    the widened arm generalizes; it must keep working.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
use core::hint::black_box as bb;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

fn put(v: u32) {
    let mut b = [0u8; 12];
    let mut i = 11usize;
    b[11] = b'\n';
    let mut x = v;
    loop {
        i -= 1;
        b[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    unsafe {
        write(1, b.as_ptr().wrapping_add(i), 12 - i);
    }
}

static EMPTY: [u16; 0] = [];
static SCALARS: [u16; 6] = [11, 22, 33, 44, 55, 66];
static NESTED: [[u8; 4]; 3] = [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]];

#[inline(never)]
fn zero_len(a: &[u16; 0]) -> usize {
    let s: &[u16] = a;
    s.len()
}

#[inline(never)]
fn thin_array_ref(a: &[u16; 6], i: usize) -> u32 {
    a[i] as u32
}

#[inline(never)]
fn slice_sum(s: &[u16]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0usize;
    while i < s.len() {
        acc = acc.wrapping_mul(7).wrapping_add(s[i] as u32);
        i += 1;
    }
    acc
}

#[inline(never)]
fn nested(t: &[[u8; 4]; 3], r: usize, c: usize) -> u32 {
    t[r][c] as u32
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    put(zero_len(&EMPTY) as u32);
    acc = acc.wrapping_mul(13).wrapping_add(zero_len(&EMPTY) as u32);
    let mut i = bb(0usize);
    while i < 6 {
        put(thin_array_ref(&SCALARS, i));
        acc = acc
            .wrapping_mul(13)
            .wrapping_add(thin_array_ref(&SCALARS, i));
        i += 1;
    }
    let s: &[u16] = &SCALARS;
    put(slice_sum(s) % 100000);
    acc = acc.wrapping_mul(13).wrapping_add(slice_sum(s));
    let mut r = bb(0usize);
    while r < 3 {
        let mut c = bb(0usize);
        while c < 4 {
            put(nested(&NESTED, r, c));
            acc = acc.wrapping_mul(13).wrapping_add(nested(&NESTED, r, c));
            c += 1;
        }
        r += 1;
    }
    put(acc % 1000);
    (acc % 83) as i32
}
