extern crate value_layout_types;
use value_layout_types::*;
unsafe extern "Rust" {
    fn byte_size(p: &[u8]) -> usize;
    fn byte_align(p: &[u8]) -> usize;
    fn byte_mut_size(p: &mut [u8]) -> usize;
    fn byte_mut_align(p: &mut [u8]) -> usize;
    fn byte_raw_size(p: *const [u8]) -> usize;
    fn byte_raw_align(p: *const [u8]) -> usize;
    fn byte_sized_size(p: &u8) -> usize;
    fn byte_sized_align(p: &u8) -> usize;
    fn byte_sized_raw_size(p: *const u8) -> usize;
    fn byte_sized_raw_align(p: *const u8) -> usize;
    fn byte_choose(p: &[u8], q: &[u8], first: bool) -> usize;
    fn byte_field_size(p: &Pair<'_, u8>) -> usize;
    fn byte_field_align(p: &Pair<'_, u8>) -> usize;
    fn byte_parts(p: *const u8, n: usize) -> usize;
    fn byte_sum(p: &[u8], q: &[u8], n: usize) -> usize;
    fn word_size(p: &[u16]) -> usize;
    fn word_align(p: &[u16]) -> usize;
    fn word_mut_size(p: &mut [u16]) -> usize;
    fn word_mut_align(p: &mut [u16]) -> usize;
    fn word_raw_size(p: *const [u16]) -> usize;
    fn word_raw_align(p: *const [u16]) -> usize;
    fn word_sized_size(p: &u16) -> usize;
    fn word_sized_align(p: &u16) -> usize;
    fn word_sized_raw_size(p: *const u16) -> usize;
    fn word_sized_raw_align(p: *const u16) -> usize;
    fn word_choose(p: &[u16], q: &[u16], first: bool) -> usize;
    fn word_field_size(p: &Pair<'_, u16>) -> usize;
    fn word_field_align(p: &Pair<'_, u16>) -> usize;
    fn word_parts(p: *const u16, n: usize) -> usize;
    fn word_sum(p: &[u16], q: &[u16], n: usize) -> usize;
    fn quad_size(p: &[u128]) -> usize;
    fn quad_align(p: &[u128]) -> usize;
    fn quad_mut_size(p: &mut [u128]) -> usize;
    fn quad_mut_align(p: &mut [u128]) -> usize;
    fn quad_raw_size(p: *const [u128]) -> usize;
    fn quad_raw_align(p: *const [u128]) -> usize;
    fn quad_sized_size(p: &u128) -> usize;
    fn quad_sized_align(p: &u128) -> usize;
    fn quad_sized_raw_size(p: *const u128) -> usize;
    fn quad_sized_raw_align(p: *const u128) -> usize;
    fn quad_choose(p: &[u128], q: &[u128], first: bool) -> usize;
    fn quad_field_size(p: &Pair<'_, u128>) -> usize;
    fn quad_field_align(p: &Pair<'_, u128>) -> usize;
    fn quad_parts(p: *const u128, n: usize) -> usize;
    fn quad_sum(p: &[u128], q: &[u128], n: usize) -> usize;
    fn pod_size(p: &[Pod]) -> usize;
    fn pod_align(p: &[Pod]) -> usize;
    fn pod_mut_size(p: &mut [Pod]) -> usize;
    fn pod_mut_align(p: &mut [Pod]) -> usize;
    fn pod_raw_size(p: *const [Pod]) -> usize;
    fn pod_raw_align(p: *const [Pod]) -> usize;
    fn pod_sized_size(p: &Pod) -> usize;
    fn pod_sized_align(p: &Pod) -> usize;
    fn pod_sized_raw_size(p: *const Pod) -> usize;
    fn pod_sized_raw_align(p: *const Pod) -> usize;
    fn pod_choose(p: &[Pod], q: &[Pod], first: bool) -> usize;
    fn pod_field_size(p: &Pair<'_, Pod>) -> usize;
    fn pod_field_align(p: &Pair<'_, Pod>) -> usize;
    fn pod_parts(p: *const Pod, n: usize) -> usize;
    fn pod_sum(p: &[Pod], q: &[Pod], n: usize) -> usize;
    fn packed_size(p: &[Packed]) -> usize;
    fn packed_align(p: &[Packed]) -> usize;
    fn packed_mut_size(p: &mut [Packed]) -> usize;
    fn packed_mut_align(p: &mut [Packed]) -> usize;
    fn packed_raw_size(p: *const [Packed]) -> usize;
    fn packed_raw_align(p: *const [Packed]) -> usize;
    fn packed_sized_size(p: &Packed) -> usize;
    fn packed_sized_align(p: &Packed) -> usize;
    fn packed_sized_raw_size(p: *const Packed) -> usize;
    fn packed_sized_raw_align(p: *const Packed) -> usize;
    fn packed_choose(p: &[Packed], q: &[Packed], first: bool) -> usize;
    fn packed_field_size(p: &Pair<'_, Packed>) -> usize;
    fn packed_field_align(p: &Pair<'_, Packed>) -> usize;
    fn packed_parts(p: *const Packed, n: usize) -> usize;
    fn packed_sum(p: &[Packed], q: &[Packed], n: usize) -> usize;
    fn wide_size(p: &[Wide]) -> usize;
    fn wide_align(p: &[Wide]) -> usize;
    fn wide_mut_size(p: &mut [Wide]) -> usize;
    fn wide_mut_align(p: &mut [Wide]) -> usize;
    fn wide_raw_size(p: *const [Wide]) -> usize;
    fn wide_raw_align(p: *const [Wide]) -> usize;
    fn wide_sized_size(p: &Wide) -> usize;
    fn wide_sized_align(p: &Wide) -> usize;
    fn wide_sized_raw_size(p: *const Wide) -> usize;
    fn wide_sized_raw_align(p: *const Wide) -> usize;
    fn wide_choose(p: &[Wide], q: &[Wide], first: bool) -> usize;
    fn wide_field_size(p: &Pair<'_, Wide>) -> usize;
    fn wide_field_align(p: &Pair<'_, Wide>) -> usize;
    fn wide_parts(p: *const Wide, n: usize) -> usize;
    fn wide_sum(p: &[Wide], q: &[Wide], n: usize) -> usize;
    fn empty_size(p: &[Empty]) -> usize;
    fn empty_align(p: &[Empty]) -> usize;
    fn empty_mut_size(p: &mut [Empty]) -> usize;
    fn empty_mut_align(p: &mut [Empty]) -> usize;
    fn empty_raw_size(p: *const [Empty]) -> usize;
    fn empty_raw_align(p: *const [Empty]) -> usize;
    fn empty_sized_size(p: &Empty) -> usize;
    fn empty_sized_align(p: &Empty) -> usize;
    fn empty_sized_raw_size(p: *const Empty) -> usize;
    fn empty_sized_raw_align(p: *const Empty) -> usize;
    fn empty_choose(p: &[Empty], q: &[Empty], first: bool) -> usize;
    fn empty_field_size(p: &Pair<'_, Empty>) -> usize;
    fn empty_field_align(p: &Pair<'_, Empty>) -> usize;
    fn empty_parts(p: *const Empty, n: usize) -> usize;
    fn empty_sum(p: &[Empty], q: &[Empty], n: usize) -> usize;
    fn text_size(p: &str) -> usize;
    fn text_align(p: &str) -> usize;
    fn text_raw_size(p: *const str) -> usize;
    fn text_raw_align(p: *const str) -> usize;
    fn text_choose(p: &str, q: &str, first: bool) -> usize;
    fn text_field_size(p: &StrPair<'_>) -> usize;
    fn text_field_align(p: &StrPair<'_>) -> usize;
}
fn main() {
    let mut checks = 0u64;
    {
        let mut check = |a: usize, b: usize| {
            assert_eq!(a, b, "check {checks}");
            checks += 1;
        };
        unsafe {
            {
                let storage = [0u8; 258];
                let other = [0u8; 258];
                let mut writable = [0u8; 258];
                check(byte_sized_size(&storage[0]), 1);
                check(byte_sized_align(&storage[0]), 1);
                check(byte_sized_raw_size(storage.as_ptr()), 1);
                check(byte_sized_raw_align(storage.as_ptr()), 1);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(byte_size(p), n * 1);
                    check(byte_align(p), 1);
                    check(byte_raw_size(p as *const [_]), n * 1);
                    check(byte_raw_align(p as *const [_]), 1);
                    check(byte_mut_size(&mut writable[..n]), n * 1);
                    check(byte_mut_align(&mut writable[..n]), 1);
                    check(byte_parts(storage.as_ptr(), n), n * 1);
                    check(byte_choose(p, q, true), n * 1);
                    check(byte_choose(p, q, false), (257 - n) * 1);
                    check(byte_field_size(&pair), (257 - n) * 1);
                    check(byte_field_align(&pair), 1);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 1;
                    check(byte_sum(p, q, count), expected);
                }
            }
            {
                let storage = [0u16; 258];
                let other = [0u16; 258];
                let mut writable = [0u16; 258];
                check(word_sized_size(&storage[0]), 2);
                check(word_sized_align(&storage[0]), 2);
                check(word_sized_raw_size(storage.as_ptr()), 2);
                check(word_sized_raw_align(storage.as_ptr()), 2);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(word_size(p), n * 2);
                    check(word_align(p), 2);
                    check(word_raw_size(p as *const [_]), n * 2);
                    check(word_raw_align(p as *const [_]), 2);
                    check(word_mut_size(&mut writable[..n]), n * 2);
                    check(word_mut_align(&mut writable[..n]), 2);
                    check(word_parts(storage.as_ptr(), n), n * 2);
                    check(word_choose(p, q, true), n * 2);
                    check(word_choose(p, q, false), (257 - n) * 2);
                    check(word_field_size(&pair), (257 - n) * 2);
                    check(word_field_align(&pair), 2);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 2;
                    check(word_sum(p, q, count), expected);
                }
            }
            {
                let storage = [0u128; 258];
                let other = [0u128; 258];
                let mut writable = [0u128; 258];
                check(quad_sized_size(&storage[0]), 16);
                check(quad_sized_align(&storage[0]), 16);
                check(quad_sized_raw_size(storage.as_ptr()), 16);
                check(quad_sized_raw_align(storage.as_ptr()), 16);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(quad_size(p), n * 16);
                    check(quad_align(p), 16);
                    check(quad_raw_size(p as *const [_]), n * 16);
                    check(quad_raw_align(p as *const [_]), 16);
                    check(quad_mut_size(&mut writable[..n]), n * 16);
                    check(quad_mut_align(&mut writable[..n]), 16);
                    check(quad_parts(storage.as_ptr(), n), n * 16);
                    check(quad_choose(p, q, true), n * 16);
                    check(quad_choose(p, q, false), (257 - n) * 16);
                    check(quad_field_size(&pair), (257 - n) * 16);
                    check(quad_field_align(&pair), 16);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 16;
                    check(quad_sum(p, q, count), expected);
                }
            }
            {
                let storage = [Pod { a: 3, b: 5, c: 7 }; 258];
                let other = [Pod { a: 3, b: 5, c: 7 }; 258];
                let mut writable = [Pod { a: 3, b: 5, c: 7 }; 258];
                check(pod_sized_size(&storage[0]), 24);
                check(pod_sized_align(&storage[0]), 8);
                check(pod_sized_raw_size(storage.as_ptr()), 24);
                check(pod_sized_raw_align(storage.as_ptr()), 8);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(pod_size(p), n * 24);
                    check(pod_align(p), 8);
                    check(pod_raw_size(p as *const [_]), n * 24);
                    check(pod_raw_align(p as *const [_]), 8);
                    check(pod_mut_size(&mut writable[..n]), n * 24);
                    check(pod_mut_align(&mut writable[..n]), 8);
                    check(pod_parts(storage.as_ptr(), n), n * 24);
                    check(pod_choose(p, q, true), n * 24);
                    check(pod_choose(p, q, false), (257 - n) * 24);
                    check(pod_field_size(&pair), (257 - n) * 24);
                    check(pod_field_align(&pair), 8);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 24;
                    check(pod_sum(p, q, count), expected);
                }
            }
            {
                let storage = [Packed { a: 3, b: 5 }; 258];
                let other = [Packed { a: 3, b: 5 }; 258];
                let mut writable = [Packed { a: 3, b: 5 }; 258];
                check(packed_sized_size(&storage[0]), 5);
                check(packed_sized_align(&storage[0]), 1);
                check(packed_sized_raw_size(storage.as_ptr()), 5);
                check(packed_sized_raw_align(storage.as_ptr()), 1);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(packed_size(p), n * 5);
                    check(packed_align(p), 1);
                    check(packed_raw_size(p as *const [_]), n * 5);
                    check(packed_raw_align(p as *const [_]), 1);
                    check(packed_mut_size(&mut writable[..n]), n * 5);
                    check(packed_mut_align(&mut writable[..n]), 1);
                    check(packed_parts(storage.as_ptr(), n), n * 5);
                    check(packed_choose(p, q, true), n * 5);
                    check(packed_choose(p, q, false), (257 - n) * 5);
                    check(packed_field_size(&pair), (257 - n) * 5);
                    check(packed_field_align(&pair), 1);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 5;
                    check(packed_sum(p, q, count), expected);
                }
            }
            {
                let storage = [Wide([1, 2, 3]); 258];
                let other = [Wide([1, 2, 3]); 258];
                let mut writable = [Wide([1, 2, 3]); 258];
                check(wide_sized_size(&storage[0]), 64);
                check(wide_sized_align(&storage[0]), 64);
                check(wide_sized_raw_size(storage.as_ptr()), 64);
                check(wide_sized_raw_align(storage.as_ptr()), 64);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(wide_size(p), n * 64);
                    check(wide_align(p), 64);
                    check(wide_raw_size(p as *const [_]), n * 64);
                    check(wide_raw_align(p as *const [_]), 64);
                    check(wide_mut_size(&mut writable[..n]), n * 64);
                    check(wide_mut_align(&mut writable[..n]), 64);
                    check(wide_parts(storage.as_ptr(), n), n * 64);
                    check(wide_choose(p, q, true), n * 64);
                    check(wide_choose(p, q, false), (257 - n) * 64);
                    check(wide_field_size(&pair), (257 - n) * 64);
                    check(wide_field_align(&pair), 64);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 64;
                    check(wide_sum(p, q, count), expected);
                }
            }
            {
                let storage = [Empty; 258];
                let other = [Empty; 258];
                let mut writable = [Empty; 258];
                check(empty_sized_size(&storage[0]), 0);
                check(empty_sized_align(&storage[0]), 32);
                check(empty_sized_raw_size(storage.as_ptr()), 0);
                check(empty_sized_raw_align(storage.as_ptr()), 32);
                for n in 0..=257 {
                    let p = &storage[..n];
                    let q = &other[..257 - n];
                    let pair = Pair {
                        first: p,
                        second: q,
                    };
                    check(empty_size(p), n * 0);
                    check(empty_align(p), 32);
                    check(empty_raw_size(p as *const [_]), n * 0);
                    check(empty_raw_align(p as *const [_]), 32);
                    check(empty_mut_size(&mut writable[..n]), n * 0);
                    check(empty_mut_align(&mut writable[..n]), 32);
                    check(empty_parts(storage.as_ptr(), n), n * 0);
                    check(empty_choose(p, q, true), n * 0);
                    check(empty_choose(p, q, false), (257 - n) * 0);
                    check(empty_field_size(&pair), (257 - n) * 0);
                    check(empty_field_align(&pair), 32);
                    let count = n % 11;
                    let expected = ((count + 1) / 2 * n + count / 2 * (257 - n)) * 0;
                    check(empty_sum(p, q, count), expected);
                }
            }

            let texts = [
                "",
                "a",
                "abc",
                "abcdefg",
                "abcdefgh",
                "abcdefghi",
                "é",
                "日本語",
                "🙂",
                "a🙂é",
                "a\0z",
            ];
            for (i, p) in texts.iter().enumerate() {
                let q = texts[(i * 7 + 3) % texts.len()];
                let pair = StrPair {
                    first: p,
                    second: q,
                };
                check(text_size(p), p.len());
                check(text_align(p), 1);
                check(text_raw_size(*p as *const str), p.len());
                check(text_raw_align(*p as *const str), 1);
                check(text_choose(p, q, true), p.len());
                check(text_choose(p, q, false), q.len());
                check(text_field_size(&pair), q.len());
                check(text_field_align(&pair), 1);
            }
            for n in [
                0,
                1,
                257,
                1 << 31,
                1 << 32,
                (1usize << 63) - 1,
                1usize << 63,
                usize::MAX,
            ] {
                let p = core::ptr::slice_from_raw_parts(
                    core::ptr::NonNull::<Empty>::dangling().as_ptr(),
                    n,
                );
                check(empty_raw_size(p), 0);
                check(empty_raw_align(p), 32);
            }
        }
    }
    println!("PASS value_layout checks={checks}");
}
