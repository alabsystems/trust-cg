use aggregate_store_types::*;
use std::num::NonZeroU64;
#[repr(C)]
struct Fence<T> {
    before: [u64; 2],
    value: T,
    after: [u64; 2],
}
fn fence<T>(value: T) -> Fence<T> {
    Fence {
        before: [0x123456789abcdef0, 0xfedcba9876543210],
        value,
        after: [0x3141592653589793, 0x2718281828459045],
    }
}
fn check<T: Copy + PartialEq + std::fmt::Debug>(
    old: T,
    new: T,
    sentinel: T,
    f: unsafe extern "C" fn(*mut T, *const T, *mut T, u8),
    checks: &mut usize,
) {
    for mode in 0..5 {
        let mut d = fence(old);
        let s = fence(new);
        let mut o = fence(sentinel);
        unsafe { f(&raw mut d.value, &raw const s.value, &raw mut o.value, mode) };
        assert_eq!(d.value, if mode == 3 { old } else { new });
        assert_eq!(s.value, new);
        assert_eq!(
            o.value,
            if mode == 2 || mode == 4 {
                old
            } else {
                sentinel
            }
        );
        for (a, b) in [
            (d.before, d.after),
            (s.before, s.after),
            (o.before, o.after),
        ] {
            assert_eq!(a, [0x123456789abcdef0, 0xfedcba9876543210]);
            assert_eq!(b, [0x3141592653589793, 0x2718281828459045]);
        }
        *checks += 1;
    }
}
unsafe extern "C" {
    fn store_pad(dst: *mut Pad, src: *const Pad, out: *mut Pad, mode: u8);
    fn store_nested(dst: *mut Nested, src: *const Nested, out: *mut Nested, mode: u8);
    fn store_rustnested(
        dst: *mut RustNested,
        src: *const RustNested,
        out: *mut RustNested,
        mode: u8,
    );
    fn store_tuple(dst: *mut Tuple, src: *const Tuple, out: *mut Tuple, mode: u8);
    fn store_array(dst: *mut Array, src: *const Array, out: *mut Array, mode: u8);
    fn store_packed(dst: *mut Packed, src: *const Packed, out: *mut Packed, mode: u8);
    fn store_wide(dst: *mut Wide, src: *const Wide, out: *mut Wide, mode: u8);
    fn store_tagged(dst: *mut Tagged, src: *const Tagged, out: *mut Tagged, mode: u8);
    fn store_niche(dst: *mut Niche, src: *const Niche, out: *mut Niche, mode: u8);
    fn store_fat(dst: *mut Fat, src: *const Fat, out: *mut Fat, mode: u8);
    fn store_zst(dst: *mut Zst, src: *const Zst, out: *mut Zst, mode: u8);
    fn store_single(dst: *mut Single, src: *const Single, out: *mut Single, mode: u8);
}
fn inner(v: u64) -> Inner {
    Inner {
        a: v.rotate_left(17),
        b: v as u32,
        c: (v >> 35) as u8,
    }
}
static BYTES: [u8; 17] = [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
];
fn main() {
    let mut checks = 0;
    for i in 0..1024_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        let values = [v, v.wrapping_add(0x123456789), !v];
        let [a, b, c] = values.map(|v| Pad {
            a: v as u8,
            b: v.rotate_left(11),
            c: (v >> 19) as u16,
        });
        check(a, b, c, store_pad, &mut checks);
        let [a, b, c] = values.map(|v| Nested {
            head: v as u8,
            inner: inner(v),
            tail: (v >> 43) as u16,
        });
        check(a, b, c, store_nested, &mut checks);
        let [a, b, c] = values.map(|v| RustNested {
            head: (v >> 17) as u8,
            inner: [v as u32, (v >> 32) as u32, !(v as u32)],
            tail: (v >> 21) as u16,
        });
        check(a, b, c, store_rustnested, &mut checks);
        let [a, b, c] = values.map(|v| Tuple {
            inner: ((v >> 31) as u8, v.rotate_left(23), v as u32),
            tail: (v >> 11) as u16,
        });
        check(a, b, c, store_tuple, &mut checks);
        let [a, b, c] = values.map(|v| Array {
            inner: [
                [v as u16, (v >> 16) as u16, (v >> 32) as u16],
                [(v >> 48) as u16, !v as u16, 0x1234],
                [0x5678, 0xabcd, (v >> 7) as u16],
            ],
        });
        check(a, b, c, store_array, &mut checks);
        let [a, b, c] = values.map(|v| Packed {
            head: v as u8,
            inner: [v as u32, (v >> 32) as u32, !(v as u32)],
            tail: (v >> 11) as u16,
        });
        check(a, b, c, store_packed, &mut checks);
        let [a, b, c] = values.map(|v| Wide {
            head: v as u8,
            inner: ((v as u128) << 64) | (!v as u128),
            tail: [v as u16, (v >> 16) as u16, (v >> 32) as u16],
        });
        check(a, b, c, store_wide, &mut checks);
        let [a, b, c] = values.map(|v| match v % 3 {
            0 => Tagged::Empty,
            1 => Tagged::Left {
                inner: inner(v),
                tail: v as u16,
            },
            _ => Tagged::Right {
                data: [v, v.rotate_left(13), !v],
            },
        });
        check(a, b, c, store_tagged, &mut checks);
        let [a, b, c] = values.map(|v| Niche {
            inner: if v & 1 == 0 {
                None
            } else {
                Some(Pair {
                    a: NonZeroU64::new(v | 1).unwrap(),
                    b: !v,
                })
            },
            tail: v as u16,
        });
        check(a, b, c, store_niche, &mut checks);
        let [a, b, c] = values.map(|v| Fat {
            data: &BYTES[(v % 7) as usize..((v % 7) + 1 + (v % 10)) as usize],
            text: if v & 1 == 0 { "alpha" } else { "λβx" },
            tail: v,
        });
        check(a, b, c, store_fat, &mut checks);
        let [a, b, c] = values.map(|v| Zst {
            first: (),
            inner: inner(v),
            last: std::marker::PhantomData,
        });
        check(a, b, c, store_zst, &mut checks);
        let [a, b, c] = values.map(|v| Single::Payload {
            inner: inner(v),
            tail: !v,
        });
        check(a, b, c, store_single, &mut checks);
    }
    println!("PASS aggregate_store checks={checks}");
}
