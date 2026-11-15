use std::cell::RefCell;
use std::panic::{AssertUnwindSafe, catch_unwind};
#[repr(C)]
#[derive(Debug)]
pub struct Record {
    pub a: u64,
    pub b: u64,
}
unsafe extern "Rust" {
    fn stored_field(a: &mut Record, n: u64, tag: u64) -> u64;
    fn borrowed_enum(x: u64, y: u64, tag: u64) -> u64;
    fn borrowed_holder(bytes: &[u8], tag: u64) -> u64;
    fn replaced_pointer(a: &[u8; 4], b: &[u8; 4]) -> u16;
    fn debug_address(a: &[u8; 4], tag: u64);
    fn mutable_array(a: &mut [u8; 4], n: u8);
    fn assert_drop(a: [u8; 4], b: &[u8], tag: u64);
    fn load16(p: *const [u8; 2]) -> u16;
    fn load32(p: *const [u8; 4]) -> u32;
    fn load64(p: *const [u8; 8]) -> u64;
    fn load128(p: *const [u8; 16]) -> u128;
    fn debug_array(a: &[u8; 4], tag: u64);
    fn debug_words(a: &[u64; 3], tag: u64);
    fn debug_empty(a: &[u8; 0], tag: u64);
    fn debug_slice(a: &[u8], tag: u64);
    fn debug_nested(a: &[u8; 4], tag: u64);
    fn assert_slice(expected: [u8; 4], actual: &[u8]);
    fn assert_arrays(expected: &[u64; 3], actual: &[u64; 3]);
    fn array_ref_identity(a: &[u8; 4]) -> bool;
}
thread_local! { static EXPECTED: RefCell<(String,u64,usize)> = const { RefCell::new((String::new(),0,0)) }; }
#[unsafe(no_mangle)]
pub fn inspect_debug(value: &dyn core::fmt::Debug, tag: u64) {
    EXPECTED.with(|e| {
        let mut e = e.borrow_mut();
        assert_eq!(format!("{value:?}"), e.0);
        assert_eq!(tag, e.1);
        e.2 += 1;
    });
}
thread_local! { static DROPS: RefCell<Vec<(u64,u64)>> = const { RefCell::new(Vec::new()) }; }
#[unsafe(no_mangle)]
pub fn report_drop(a: u64, b: u64) {
    DROPS.with(|d| d.borrow_mut().push((a, b)));
}
#[unsafe(no_mangle)]
pub fn inspect_debug_address(value: &dyn core::fmt::Debug, expected: *const (), tag: u64) {
    assert_eq!(value as *const dyn core::fmt::Debug as *const (), expected);
    inspect_debug(value, tag);
}
fn expect_debug(s: String, tag: u64, f: impl FnOnce()) {
    EXPECTED.with(|e| *e.borrow_mut() = (s, tag, 0));
    f();
    EXPECTED.with(|e| assert_eq!(e.borrow().2, 1));
}
fn message(f: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected panic");
    *payload.downcast::<String>().expect("String panic payload")
}
fn main() {
    if std::env::args().any(|s| s == "abort") {
        unsafe {
            assert_drop([1, 2, 3, 4], &[1, 2, 4, 3], 7);
        }
        panic!("assertion returned");
    }
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for seed in 0u64..128 {
        let a = [
            seed as u8,
            seed.wrapping_mul(19) as u8,
            255 - seed as u8,
            seed.wrapping_mul(113) as u8,
        ];
        let w = [seed, u64::MAX - seed, seed.wrapping_mul(0x123456789abcdef)];
        unsafe {
            expect_debug(format!("{a:?}"), seed, || debug_array(&a, seed));
            checks += 1;
            expect_debug(format!("{w:?}"), seed, || debug_words(&w, seed));
            checks += 1;
            expect_debug("[]".to_string(), seed, || debug_empty(&[], seed));
            checks += 1;
            expect_debug(format!("{:?}", &a[1..]), seed, || {
                debug_slice(&a[1..], seed)
            });
            checks += 1;
            expect_debug(format!("{a:?}"), seed, || debug_nested(&a, seed));
            checks += 1;
            assert!(array_ref_identity(&a));
            checks += 1;
            expect_debug(
                format!("Holder {{ bytes: {:?}, word: {seed} }}", &a[1..]),
                seed,
                || {
                    assert_eq!(borrowed_holder(&a[1..], seed), 3 ^ seed);
                },
            );
            checks += 1;
            let (description, result) = match seed % 3 {
                0 => ("Empty".to_string(), 1),
                1 => (format!("One({})", w[1]), w[1] ^ 2),
                _ => (
                    format!("Two({}, {})", w[1], w[2]),
                    w[1].wrapping_add(w[2]) ^ 3,
                ),
            };
            expect_debug(description, seed, || {
                assert_eq!(borrowed_enum(w[1], w[2], seed), result)
            });
            checks += 1;
            let mut record = Record { a: w[0], b: w[1] };
            expect_debug(format!("{record:?}"), seed, || {
                assert_eq!(stored_field(&mut record, w[2], seed), w[1]);
            });
            assert_eq!(record.a, w[2]);
            assert_eq!(record.b, w[1]);
            checks += 1;
            expect_debug(format!("{a:?}"), seed, || debug_address(&a, seed));
            checks += 1;
            let other = [a[0] ^ 0xff, a[1], a[2], a[3] ^ 0x55];
            assert_eq!(
                replaced_pointer(&a, &other),
                u16::from(other[0]) * 256 + u16::from(other[3])
            );
            checks += 1;
            let mut m = a;
            mutable_array(&mut m, seed as u8 ^ 127);
            assert_eq!(m, [a[0], a[1], seed as u8 ^ 127, a[3]]);
            checks += 1;
            let bytes: Vec<u8> = (0..48)
                .map(|i| (seed.wrapping_mul(113).wrapping_add(i * 37)) as u8)
                .collect();
            for offset in 0..=16 {
                let p = bytes.as_ptr().add(offset);
                assert_eq!(
                    load16(p.cast()),
                    u16::from_ne_bytes(bytes[offset..offset + 2].try_into().unwrap())
                );
                assert_eq!(
                    load32(p.cast()),
                    u32::from_ne_bytes(bytes[offset..offset + 4].try_into().unwrap())
                );
                assert_eq!(
                    load64(p.cast()),
                    u64::from_ne_bytes(bytes[offset..offset + 8].try_into().unwrap())
                );
                assert_eq!(
                    load128(p.cast()),
                    u128::from_ne_bytes(bytes[offset..offset + 16].try_into().unwrap())
                );
                checks += 4;
            }
            assert_slice(a, &a);
            checks += 1;
            DROPS.with(|d| d.borrow_mut().clear());
            assert_drop(a, &a, seed);
            DROPS.with(|d| assert_eq!(*d.borrow(), vec![(seed, seed ^ 0xabcdef)]));
            checks += 1;
            assert_arrays(&w, &w);
            checks += 1;
            if cfg!(panic = "unwind") {
                let b = [a[0] ^ 255, a[1], a[2], a[3]];
                assert_eq!(
                    message(|| assert_slice(a, &b)),
                    format!("assertion `left == right` failed\n  left: {a:?}\n right: {b:?}")
                );
                checks += 1;
                DROPS.with(|d| d.borrow_mut().clear());
                assert_eq!(
                    message(|| assert_drop(a, &b, seed)),
                    format!("assertion `left == right` failed\n  left: {a:?}\n right: {b:?}")
                );
                DROPS.with(|d| assert_eq!(*d.borrow(), vec![(seed, seed ^ 0xabcdef)]));
                checks += 1;
                let v = [w[0], w[1] ^ 1, w[2]];
                assert_eq!(
                    message(|| assert_arrays(&w, &v)),
                    format!("assertion `left == right` failed\n  left: {w:?}\n right: {v:?}")
                );
                checks += 1;
            }
        }
    }
    println!("PASS assert_pointer checks={checks}");
}
