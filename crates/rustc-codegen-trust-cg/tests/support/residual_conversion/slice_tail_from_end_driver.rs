unsafe extern "Rust" {
    fn tail_word(words: &[u64]) -> u64;
    fn end_words(words: &[u64]) -> u64;
    fn tail_mut(words: &mut [u64], mask: u64) -> u64;
}
fn part_0() {
    let mut checks = 0;
    for len in 0..128usize {
        let mut words: Vec<u64> = (0..len)
            .map(|n| (n as u64).wrapping_mul(0x9e3779b97f4a7c15))
            .collect();
        assert_eq!(
            unsafe { tail_word(&words) },
            words.last().copied().unwrap_or(0)
        );
        checks += 1;
        assert_eq!(
            unsafe { end_words(&words) },
            if len >= 2 {
                words[0] ^ words[len - 1]
            } else {
                0
            }
        );
        checks += 1;
        let mut expected = words.clone();
        if let Some(x) = expected.last_mut() {
            *x ^= 0xa5a5a5a5a5a5a5a5;
        }
        assert_eq!(
            unsafe { tail_mut(&mut words, 0xa5a5a5a5a5a5a5a5) },
            expected.last().copied().unwrap_or(0)
        );
        checks += 1;
        assert_eq!(words, expected);
        checks += 1;
    }
    println!("PASS slice_from_end checks={checks}");
}

#[repr(transparent)]
struct Bytes([u8]);
unsafe extern "Rust" {
    fn tail_wrapped(bytes: &Bytes) -> u8;
    fn trim_wrapped(bytes: &Bytes) -> usize;
}
fn part_1() {
    let mut checks = 0;
    for text in ["", "/", "//", "abc", "abc/", "abc//", "abc/d", "abc/d///"] {
        let bytes = unsafe { &*(text.as_bytes() as *const [u8] as *const Bytes) };
        assert_eq!(
            unsafe { tail_wrapped(bytes) },
            text.as_bytes().last().copied().unwrap_or(0)
        );
        checks += 1;
        assert_eq!(
            unsafe { trim_wrapped(bytes) },
            text.trim_end_matches('/').len()
        );
        checks += 1;
    }
    println!("PASS slice_from_end_wrapped checks={checks}");
}

#[repr(C)]
struct Head<T: ?Sized> {
    marker: u64,
    tail: T,
}
#[repr(C)]
struct Outer<T: ?Sized> {
    marker: u64,
    inner: Head<T>,
}
#[repr(C)]
#[derive(Copy, Clone)]
struct Pair {
    a: u64,
    b: u64,
}
unsafe extern "Rust" {
    fn last_u64(data: &Head<[u64]>) -> u64;
    fn last_two(data: &Head<[u16]>) -> u64;
    fn mutate_last(data: &mut Head<[u64]>, mask: u64) -> u64;
    fn raw_read(data: *const Head<[u64]>) -> u64;
    fn raw_write(data: *mut Head<[u64]>, mask: u64) -> u64;
    fn nested_last(data: &Outer<[u64]>) -> u64;
    fn borrow_last(data: &Head<[u64]>) -> &u64;
    fn pointer_last(data: &Head<[u64]>) -> *const u64;
    fn pair_last(data: &Head<[Pair]>) -> *const Pair;
}
fn part_2() {
    let mut checks = 0;
    for seed in 0..128u64 {
        for len in 0..=16 {
            let words = std::array::from_fn::<_, 16, _>(|i| {
                (seed ^ (i as u64)).wrapping_mul(0x9e3779b97f4a7c15)
            });
            let mut image = Head {
                marker: seed ^ 0x55,
                tail: words,
            };
            // A repr(C) image with capacity 16 and metadata len exposes its prefix and
            // exactly len initialized tail elements; the allocation outlives each view.
            let expected = if len == 0 {
                image.marker
            } else {
                words[len - 1]
            };
            let expected_ptr = if len == 0 {
                &image.marker as *const u64
            } else {
                &image.tail[len - 1] as *const u64
            };
            let ptr = std::ptr::slice_from_raw_parts_mut(
                (&mut image as *mut Head<[u64; 16]>).cast::<u64>(),
                len,
            ) as *mut Head<[u64]>;
            assert_eq!(unsafe { last_u64(&*ptr) }, expected);
            checks += 1;
            assert_eq!(unsafe { raw_read(ptr) }, expected);
            checks += 1;
            assert_eq!(unsafe { borrow_last(&*ptr) } as *const u64, expected_ptr);
            checks += 1;
            assert_eq!(unsafe { pointer_last(&*ptr) }, expected_ptr);
            checks += 1;
            assert_eq!(
                unsafe { mutate_last(&mut *ptr, 0xa5a5a5a5a5a5a5a5) },
                expected
            );
            checks += 1;
            assert_eq!(
                unsafe { raw_write(ptr, 0xa5a5a5a5a5a5a5a5) },
                if len == 0 {
                    expected
                } else {
                    expected ^ 0xa5a5a5a5a5a5a5a5
                }
            );
            checks += 1;
            assert_eq!(image.tail, words);
            assert_eq!(image.marker, seed ^ 0x55);
            checks += 2;
            let shorts = Head {
                marker: seed ^ 0x33,
                tail: std::array::from_fn::<_, 16, _>(|i| {
                    ((seed as usize * 113 + i * 769) & 65535) as u16
                }),
            };
            let short_ptr = std::ptr::slice_from_raw_parts(
                (&shorts as *const Head<[u16; 16]>).cast::<u16>(),
                len,
            ) as *const Head<[u16]>;
            assert_eq!(
                unsafe { last_two(&*short_ptr) },
                if len < 2 {
                    shorts.marker
                } else {
                    shorts.tail[len - 2] as u64 * 65536 + shorts.tail[len - 1] as u64
                }
            );
            checks += 1;
            let outer = Outer {
                marker: seed ^ 0x77,
                inner: Head {
                    marker: seed ^ 0x11,
                    tail: words,
                },
            };
            let outer_ptr = std::ptr::slice_from_raw_parts(
                (&outer as *const Outer<[u64; 16]>).cast::<u64>(),
                len,
            ) as *const Outer<[u64]>;
            assert_eq!(
                unsafe { nested_last(&*outer_ptr) },
                if len == 0 {
                    outer.inner.marker
                } else {
                    words[len - 1]
                }
            );
            checks += 1;
            let pairs = Head {
                marker: seed ^ 0x99,
                tail: std::array::from_fn::<_, 16, _>(|i| Pair {
                    a: words[i],
                    b: !words[i],
                }),
            };
            let pair_ptr = std::ptr::slice_from_raw_parts(
                (&pairs as *const Head<[Pair; 16]>).cast::<Pair>(),
                len,
            ) as *const Head<[Pair]>;
            assert_eq!(
                unsafe { pair_last(&*pair_ptr) },
                if len == 0 {
                    std::ptr::null()
                } else {
                    &pairs.tail[len - 1]
                }
            );
            checks += 1;
        }
    }
    println!("PASS slice_tail_from_end checks={checks}");
}

fn main() {
    part_0();
    part_1();
    part_2();
}
