// CORPUS FIXTURE — SIZED ARRAY value types: an array pointee whose element is a
// TUPLE CONTAINING AN ARRAY, which is the shape of
// `core::unicode::unicode_data::conversions`'s multi-character case-mapping
// table (`&'static [(u16, [u16; 3])]`) and the reason 5 `library/core` roots
// stopped on `Ty::[u16; 3_usize]` / `Ty::(u16, [u16; 3_usize])`.
//
// WHAT THIS PINS, and why the pin is ELEMENT-BY-ELEMENT rather than a checksum:
// the failure mode a lane like this introduces is not a refusal, it is a WRONG
// ELEMENT — an array lowered at the wrong stride (register width instead of
// `size_of::<T>()`), or a tuple whose rustc layout REORDERED its fields while
// the lowering assumed declaration order. Both produce a plausible number. So
// every element of every array is printed individually to stdout and compared
// against LLVM's, and the exit code additionally folds all of them.
//
// `(u16, [u16; 3])` is deliberately a shape where stride and order both matter:
// the element is 8 bytes, the inner array's stride is 2, and the `u16` key sits
// at a different offset from the array's first element.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

// A `&[T]`-indexing `no_std` binary at `-Copt-level=0` leaves libcore's own
// object referencing `_rust_eh_personality`, which `-Cpanic=abort` does not
// define; the LLVM ORACLE fails to link without this shim, so it is a property
// of the fixture shape, not of either backend. Defined identically for both
// sides of the differential.
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}

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

static TABLE: [(u16, [u16; 3]); 6] = [
    (0x0130, [0x0069, 0x0307, 0x0000]),
    (0x00DF, [0x0053, 0x0053, 0x0000]),
    (0x0587, [0x0535, 0x0552, 0x0000]),
    (0xFB03, [0x0046, 0x0046, 0x0049]),
    (0xFB04, [0x0046, 0x0046, 0x004C]),
    (0x1E96, [0x0048, 0x0331, 0x0000]),
];

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let t: &[(u16, [u16; 3])] = &TABLE;
    let mut acc: u32 = 0;
    // (1) Read EVERY key and EVERY array element THROUGH the slice reference.
    let mut r = bb(0usize);
    while r < 6 {
        let e = unsafe { t.get_unchecked(r) };
        put(e.0 as u32);
        acc = acc.wrapping_mul(31).wrapping_add(e.0 as u32);
        let mut c = bb(0usize);
        while c < 3 {
            put(e.1[c] as u32);
            acc = acc.wrapping_mul(31).wrapping_add(e.1[c] as u32);
            c += 1;
        }
        r += 1;
    }
    // (2) COPY the element out by value (`let &(k, arr) = ...`) and re-read it.
    //     This is the `conversions::lookup` spelling exactly.
    let i = bb(3usize);
    let &(k, arr) = unsafe { t.get_unchecked(i) };
    put(k as u32);
    put(arr[0] as u32);
    put(arr[1] as u32);
    put(arr[2] as u32);
    acc = acc.wrapping_mul(31).wrapping_add(k as u32);
    acc = acc
        .wrapping_mul(31)
        .wrapping_add(arr[0] as u32 + 3 * arr[1] as u32 + 7 * arr[2] as u32);
    // (3) Round-trip the WHOLE tuple by value through an `#[inline(never)]`
    //     callee and back, then re-read every element.
    let back = bump(bb((k, arr)));
    put(back.0 as u32);
    put(back.1[0] as u32);
    put(back.1[1] as u32);
    put(back.1[2] as u32);
    acc = acc.wrapping_mul(31).wrapping_add(back.0 as u32);
    acc = acc.wrapping_mul(31).wrapping_add(back.1[2] as u32);
    put(acc % 1000);
    (acc % 97) as i32
}

#[inline(never)]
fn bump(e: (u16, [u16; 3])) -> (u16, [u16; 3]) {
    (
        e.0.wrapping_add(1),
        [
            e.1[0].wrapping_add(1),
            e.1[1].wrapping_add(2),
            e.1[2].wrapping_add(3),
        ],
    )
}
