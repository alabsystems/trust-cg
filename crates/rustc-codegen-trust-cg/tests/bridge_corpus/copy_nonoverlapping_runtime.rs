// CORPUS FIXTURE — `core::ptr::copy_nonoverlapping` with a RUNTIME count (and the
// dead panic-format machinery its safety precondition drags in).
//
// Before this lowering the intrinsic fail-closed whenever the count operand was a
// runtime value ("copy_nonoverlapping count is not a compile-time constant"), and
// even the const-count uses fail-closed at -O0: the non-inlined library wrapper
// `core::ptr::copy_nonoverlapping::<T>` carries the runtime-count intrinsic AND its
// `assert_unsafe_precondition!` collects `<*const T>::is_aligned_to` /
// `ub_checks::maybe_is_nonoverlapping`, whose dead panic arms build the unmodelable
// `core::fmt::rt::ArgumentType`.
//
// Two fixes make this compile end-to-end at every opt level:
//   * a runtime (or non-scalar / over-large) count lowers to a libc `memcpy(dst,
//     src, count*size_of::<T>())` call — memcpy's non-overlap contract is exactly
//     `copy_nonoverlapping`'s precondition, so it is a faithful lowering (what
//     rustc's own backend emits); a const scalar count still unrolls to proven
//     load/store pairs; and
//   * the panic-format blocks (a `core::panicking::*` diverging call, e.g.
//     `panic_fmt`) are trapped whole — sound under panic=abort (panic == abort ==
//     trap), which keeps `is_aligned_to` lowerable instead of dropped-to-undefined.
//
// Exercises: (a) runtime full copy; (b) runtime partial copy (tail untouched);
// (c) count=0 (no-op); (d) i8 element; (e) `<*const T>::copy_to_nonoverlapping`;
// (f) a struct (non-scalar-leaf) element. All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

#[derive(Clone, Copy)]
struct Pair {
    a: i32,
    b: i64,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) runtime full copy (count == len).
    let sa = [bb(1i64), bb(2), bb(3), bb(4)];
    let mut da = [0i64; 4];
    let na = bb(4usize);
    unsafe {
        core::ptr::copy_nonoverlapping(sa.as_ptr(), da.as_mut_ptr(), na);
    }
    let ok_a = da[0] == 1 && da[1] == 2 && da[2] == 3 && da[3] == 4;

    // (b) runtime partial copy: first 2 of 4, tail untouched.
    let sb = [bb(10i64), bb(20), bb(30), bb(40)];
    let mut db = [bb(9i64), bb(9), bb(9), bb(9)];
    let nb = bb(2usize);
    unsafe {
        core::ptr::copy_nonoverlapping(sb.as_ptr(), db.as_mut_ptr(), nb);
    }
    let ok_b = db[0] == 10 && db[1] == 20 && db[2] == 9 && db[3] == 9;

    // (c) runtime count == 0: nothing copied.
    let sc = [bb(5i64), bb(6)];
    let mut dc = [bb(7i64), bb(8)];
    let nc = bb(0usize);
    unsafe {
        core::ptr::copy_nonoverlapping(sc.as_ptr(), dc.as_mut_ptr(), nc);
    }
    let ok_c = dc[0] == 7 && dc[1] == 8;

    // (d) i8 element (elem_size == 1).
    let sd = [bb(11i8), bb(22), bb(33)];
    let mut dd = [0i8; 3];
    let nd = bb(3usize);
    unsafe {
        core::ptr::copy_nonoverlapping(sd.as_ptr(), dd.as_mut_ptr(), nd);
    }
    let ok_d = dd[0] == 11 && dd[1] == 22 && dd[2] == 33;

    // (e) the `<*const T>::copy_to_nonoverlapping` method form.
    let se = [bb(2i64), bb(4), bb(6)];
    let mut de = [0i64; 3];
    let ne = bb(3usize);
    unsafe {
        se.as_ptr().copy_to_nonoverlapping(de.as_mut_ptr(), ne);
    }
    let ok_e = de[0] == 2 && de[1] == 4 && de[2] == 6;

    // (f) a struct (non-scalar-leaf) element -> the memcpy path handles any layout.
    let sf = [
        Pair { a: bb(1), b: bb(2) },
        Pair { a: bb(3), b: bb(4) },
    ];
    let mut df = [Pair { a: 0, b: 0 }; 2];
    let nf = bb(2usize);
    unsafe {
        core::ptr::copy_nonoverlapping(sf.as_ptr(), df.as_mut_ptr(), nf);
    }
    let ok_f = df[0].a == 1 && df[0].b == 2 && df[1].a == 3 && df[1].b == 4;

    if ok_a && ok_b && ok_c && ok_d && ok_e && ok_f {
        7
    } else {
        13
    }
}
