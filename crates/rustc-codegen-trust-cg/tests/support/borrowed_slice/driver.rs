use borrowed_slice_types::*;
unsafe extern "Rust" {
    fn zero_middle(v: (u64, (&[Zero], &[Zero]))) -> (*const Zero, usize);
    fn wide_middle(v: (u64, (&[Wide], &[Wide]))) -> (*const Wide, usize);
    fn word_middle(v: (u64, (&[u64], &[u64]))) -> (*const u64, usize);
    fn byte_middle(v: (u64, (&[u8], &[u8]))) -> (*const u8, usize);
    fn byte_first(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8;
    fn byte_second(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8;
    fn byte_last(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8;
    fn byte_penultimate(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8;
    fn byte_single(v: (bool, (&[u8], &[u16], &[u8]))) -> *const u8;
    fn byte_runtime(v: (u64, (&[u8], &[u8])), index: usize) -> *const u8;
    fn byte_mutable(v: (u64, (&mut [u8], u64))) -> *mut u8;
    fn word_first(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64;
    fn word_second(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64;
    fn word_last(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64;
    fn word_penultimate(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64;
    fn word_single(v: (bool, (&[u64], &[u16], &[u64]))) -> *const u64;
    fn word_runtime(v: (u64, (&[u64], &[u64])), index: usize) -> *const u64;
    fn word_mutable(v: (u64, (&mut [u64], u64))) -> *mut u64;
    fn wide_first(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide;
    fn wide_second(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide;
    fn wide_last(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide;
    fn wide_penultimate(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide;
    fn wide_single(v: (bool, (&[Wide], &[u16], &[Wide]))) -> *const Wide;
    fn wide_runtime(v: (u64, (&[Wide], &[Wide])), index: usize) -> *const Wide;
    fn wide_mutable(v: (u64, (&mut [Wide], u64))) -> *mut Wide;
    fn zero_first(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero;
    fn zero_second(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero;
    fn zero_last(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero;
    fn zero_penultimate(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero;
    fn zero_single(v: (bool, (&[Zero], &[u16], &[Zero]))) -> *const Zero;
    fn zero_runtime(v: (u64, (&[Zero], &[Zero])), index: usize) -> *const Zero;
    fn zero_mutable(v: (u64, (&mut [Zero], u64))) -> *mut Zero;
    fn mutate_words(v: (bool, (&mut [u64], u64)), value: u64) -> bool;
    fn select_last(a: &[u64], b: &[u64], choose: bool) -> *const u64;
}
fn main() {
    let mut checks = 0u64;
    for seed in 0..256u64 {
        let bytes = core::array::from_fn::<_, 40, _>(|i| (seed.wrapping_mul(17) ^ i as u64) as u8);
        let words =
            core::array::from_fn::<_, 40, _>(|i| seed.wrapping_mul(0x9e3779b97f4a7c15) ^ i as u64);
        let wides = core::array::from_fn::<_, 40, _>(|i| Wide {
            a: words[i],
            b: !words[i],
        });
        let zeros = [Zero; 40];
        for len in 0..=32usize {
            let start = seed as usize % 8;
            {
                let slice = &bytes[start..start + len];
                let blank = &bytes[start..start];
                for flag in [false, true] {
                    for prefix in [blank, &bytes[..1]] {
                        let arg = (flag, (prefix, &[0xbeefu16][..], slice));
                        let expected = if flag && prefix.is_empty() && len >= 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { byte_first(arg) },
                            expected,
                            "byte_first seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { byte_second(arg) },
                            expected,
                            "byte_second seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { byte_last(arg) },
                            expected,
                            "byte_last seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 2) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { byte_penultimate(arg) },
                            expected,
                            "byte_penultimate seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len == 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { byte_single(arg) },
                            expected,
                            "byte_single seed={seed} len={len}"
                        );
                        checks += 1;
                    }
                }
                let expected = if len >= 2 {
                    (unsafe { slice.as_ptr().add(1) }, len - 2)
                } else {
                    (core::ptr::null(), 0)
                };
                let middle = unsafe { byte_middle((seed, (blank, slice))) };
                assert_eq!(middle.0, expected.0);
                assert_eq!(middle.1, expected.1);
                checks += 2;
                for index in [0, len / 2, len.saturating_sub(1), len, len + 1] {
                    let expected = if index < len {
                        unsafe { slice.as_ptr().add(index) }
                    } else {
                        core::ptr::null()
                    };
                    assert_eq!(
                        unsafe { byte_runtime((seed, (blank, slice)), index) },
                        expected
                    );
                    checks += 1;
                }
                let mut copy = bytes;
                let view = &mut copy[start..start + len];
                let expected = if len >= 2 {
                    unsafe { view.as_mut_ptr().add(len - 1) }
                } else {
                    core::ptr::null_mut()
                };
                assert_eq!(unsafe { byte_mutable((seed, (view, !seed))) }, expected);
                checks += 1;
            }
            {
                let slice = &words[start..start + len];
                let blank = &words[start..start];
                for flag in [false, true] {
                    for prefix in [blank, &words[..1]] {
                        let arg = (flag, (prefix, &[0xbeefu16][..], slice));
                        let expected = if flag && prefix.is_empty() && len >= 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { word_first(arg) },
                            expected,
                            "word_first seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { word_second(arg) },
                            expected,
                            "word_second seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { word_last(arg) },
                            expected,
                            "word_last seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 2) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { word_penultimate(arg) },
                            expected,
                            "word_penultimate seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len == 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { word_single(arg) },
                            expected,
                            "word_single seed={seed} len={len}"
                        );
                        checks += 1;
                    }
                }
                let expected = if len >= 2 {
                    (unsafe { slice.as_ptr().add(1) }, len - 2)
                } else {
                    (core::ptr::null(), 0)
                };
                let middle = unsafe { word_middle((seed, (blank, slice))) };
                assert_eq!(middle.0, expected.0);
                assert_eq!(middle.1, expected.1);
                checks += 2;
                for index in [0, len / 2, len.saturating_sub(1), len, len + 1] {
                    let expected = if index < len {
                        unsafe { slice.as_ptr().add(index) }
                    } else {
                        core::ptr::null()
                    };
                    assert_eq!(
                        unsafe { word_runtime((seed, (blank, slice)), index) },
                        expected
                    );
                    checks += 1;
                }
                let mut copy = words;
                let view = &mut copy[start..start + len];
                let expected = if len >= 2 {
                    unsafe { view.as_mut_ptr().add(len - 1) }
                } else {
                    core::ptr::null_mut()
                };
                assert_eq!(unsafe { word_mutable((seed, (view, !seed))) }, expected);
                checks += 1;
            }
            {
                let slice = &wides[start..start + len];
                let blank = &wides[start..start];
                for flag in [false, true] {
                    for prefix in [blank, &wides[..1]] {
                        let arg = (flag, (prefix, &[0xbeefu16][..], slice));
                        let expected = if flag && prefix.is_empty() && len >= 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { wide_first(arg) },
                            expected,
                            "wide_first seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { wide_second(arg) },
                            expected,
                            "wide_second seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { wide_last(arg) },
                            expected,
                            "wide_last seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 2) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { wide_penultimate(arg) },
                            expected,
                            "wide_penultimate seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len == 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { wide_single(arg) },
                            expected,
                            "wide_single seed={seed} len={len}"
                        );
                        checks += 1;
                    }
                }
                let expected = if len >= 2 {
                    (unsafe { slice.as_ptr().add(1) }, len - 2)
                } else {
                    (core::ptr::null(), 0)
                };
                let middle = unsafe { wide_middle((seed, (blank, slice))) };
                assert_eq!(middle.0, expected.0);
                assert_eq!(middle.1, expected.1);
                checks += 2;
                for index in [0, len / 2, len.saturating_sub(1), len, len + 1] {
                    let expected = if index < len {
                        unsafe { slice.as_ptr().add(index) }
                    } else {
                        core::ptr::null()
                    };
                    assert_eq!(
                        unsafe { wide_runtime((seed, (blank, slice)), index) },
                        expected
                    );
                    checks += 1;
                }
                let mut copy = wides;
                let view = &mut copy[start..start + len];
                let expected = if len >= 2 {
                    unsafe { view.as_mut_ptr().add(len - 1) }
                } else {
                    core::ptr::null_mut()
                };
                assert_eq!(unsafe { wide_mutable((seed, (view, !seed))) }, expected);
                checks += 1;
            }
            {
                let slice = &zeros[start..start + len];
                let blank = &zeros[start..start];
                for flag in [false, true] {
                    for prefix in [blank, &zeros[..1]] {
                        let arg = (flag, (prefix, &[0xbeefu16][..], slice));
                        let expected = if flag && prefix.is_empty() && len >= 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { zero_first(arg) },
                            expected,
                            "zero_first seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { zero_second(arg) },
                            expected,
                            "zero_second seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 1) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { zero_last(arg) },
                            expected,
                            "zero_last seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len >= 2 {
                            unsafe { slice.as_ptr().add(len - 2) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { zero_penultimate(arg) },
                            expected,
                            "zero_penultimate seed={seed} len={len}"
                        );
                        checks += 1;
                        let expected = if flag && prefix.is_empty() && len == 1 {
                            unsafe { slice.as_ptr().add(0) }
                        } else {
                            core::ptr::null()
                        };
                        assert_eq!(
                            unsafe { zero_single(arg) },
                            expected,
                            "zero_single seed={seed} len={len}"
                        );
                        checks += 1;
                    }
                }
                let expected = if len >= 2 {
                    (unsafe { slice.as_ptr().add(1) }, len - 2)
                } else {
                    (core::ptr::null(), 0)
                };
                let middle = unsafe { zero_middle((seed, (blank, slice))) };
                assert_eq!(middle.0, expected.0);
                assert_eq!(middle.1, expected.1);
                checks += 2;
                for index in [0, len / 2, len.saturating_sub(1), len, len + 1] {
                    let expected = if index < len {
                        unsafe { slice.as_ptr().add(index) }
                    } else {
                        core::ptr::null()
                    };
                    assert_eq!(
                        unsafe { zero_runtime((seed, (blank, slice)), index) },
                        expected
                    );
                    checks += 1;
                }
                let mut copy = zeros;
                let view = &mut copy[start..start + len];
                let expected = if len >= 2 {
                    unsafe { view.as_mut_ptr().add(len - 1) }
                } else {
                    core::ptr::null_mut()
                };
                assert_eq!(unsafe { zero_mutable((seed, (view, !seed))) }, expected);
                checks += 1;
            }
            for flag in [false, true] {
                let mut copy = words;
                let mut expected = words;
                let value = seed ^ 0xfeedfacecafebeef;
                if flag && len >= 2 {
                    expected[start] ^= value;
                    expected[start + len - 1] = value;
                }
                assert_eq!(
                    unsafe { mutate_words((flag, (&mut copy[start..start + len], seed)), value) },
                    flag && len >= 2
                );
                checks += 1;
                assert_eq!(copy, expected);
                checks += 1;
                let a = &words[start..start + len];
                let b = &words[1..37];
                let chosen = if flag { a } else { b };
                let ptr = if chosen.is_empty() {
                    core::ptr::null()
                } else {
                    unsafe { chosen.as_ptr().add(chosen.len() - 1) }
                };
                assert_eq!(unsafe { select_last(a, b, flag) }, ptr);
                checks += 1;
            }
        }
    }
    assert_eq!(checks, 996864);
    println!("PASS borrowed_slice checks={checks}");
}
