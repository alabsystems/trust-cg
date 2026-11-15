use core::ffi::{c_int, c_void};
use mixed_libcalls as c;
use mixed_libcall_provider as provider;

fn main() {
    let mut checks = 0usize;
    assert_eq!(provider::opaque_libcall_count(0), 0);
    for (got, expected) in [
        (core::mem::size_of::<usize>(), 8), (core::mem::align_of::<usize>(), 8),
        (core::mem::size_of::<c_int>(), 4), (core::mem::align_of::<c_int>(), 4),
        (core::mem::size_of::<*mut c_void>(), 8), (core::mem::align_of::<*mut c_void>(), 8),
    ] { assert_eq!(got, expected); }
    let source: [u8; 96] = core::array::from_fn(|i| (i * 13 + 7) as u8);
    for order in 0..2 {
        for n in [0usize, 1, 3, 15, 16, 31] {
            let mut dst = [0x55u8; 96];
            let mut expected = dst;
            expected[8..8+n].copy_from_slice(&source[4..4+n]);
            expected[48..48+n].copy_from_slice(&source[4..4+n]);
            let p = dst.as_mut_ptr();
            let returned = unsafe {
                if order == 0 { c::memcpy_intrinsic_first(p.add(8), p.add(48), source.as_ptr().add(4), n) }
                else { c::memcpy_extern_first(p.add(8), p.add(48), source.as_ptr().add(4), n) }
            };
            assert_eq!(returned.cast::<u8>(), unsafe {p.add(48)}); checks += 1;
            for i in 0..96 { assert_eq!(dst[i], expected[i], "memcpy order={order} n={n} byte={i}"); checks += 1; }
            for i in 0..96 { assert_eq!(source[i], (i * 13 + 7) as u8); checks += 1; }
        }
        for n in [0usize, 1, 3, 15, 16, 31] {
            for direction in 0..2 {
                let mut dst: [u8; 128] = core::array::from_fn(|i| (i * 17 + 3) as u8);
                let mut expected = dst;
                let (sa, da, sb, db) = if direction == 0 { (8, 11, 64, 69) } else { (11, 8, 69, 64) };
                let snapshot_a: Vec<u8> = expected[sa..sa+n].to_vec();
                expected[da..da+n].copy_from_slice(&snapshot_a);
                let snapshot_b: Vec<u8> = expected[sb..sb+n].to_vec();
                expected[db..db+n].copy_from_slice(&snapshot_b);
                let p = dst.as_mut_ptr();
                let returned = unsafe {
                    if order == 0 { c::memmove_intrinsic_first(p.add(da), p.add(sa), p.add(db), p.add(sb), n) }
                    else { c::memmove_extern_first(p.add(da), p.add(sa), p.add(db), p.add(sb), n) }
                };
                assert_eq!(returned.cast::<u8>(), unsafe {p.add(db)}); checks += 1;
                for i in 0..128 { assert_eq!(dst[i], expected[i], "memmove order={order} n={n} dir={direction} byte={i}"); checks += 1; }
            }
        }
        for n in [0usize, 1, 3, 15, 16, 31] {
            for value in [0 as c_int, 0x7f, 0xff, 0x123, -1, -128, -257] {
                let mut dst = [0x55u8; 96];
                let mut expected = dst;
                expected[8..8+n].fill(value as u8);
                expected[48..48+n].fill(value as u8);
                let p = dst.as_mut_ptr();
                let returned = unsafe {
                    if order == 0 { c::memset_intrinsic_first(p.add(8), p.add(48), value, n) }
                    else { c::memset_extern_first(p.add(8), p.add(48), value, n) }
                };
                assert_eq!(returned.cast::<u8>(), unsafe {p.add(48)}); checks += 1;
                for i in 0..96 { assert_eq!(dst[i], expected[i], "memset order={order} n={n} c={value} byte={i}"); checks += 1; }
            }
        }
    }
    assert_eq!(checks, 13560);
    println!("MIXED_LIBCALLS|checks={checks}|layouts=6|runtime_count=LLVM|families=3|orders=2");
}
