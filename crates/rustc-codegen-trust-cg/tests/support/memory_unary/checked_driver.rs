mod types;
use types::{Outer, Pair};
unsafe extern "Rust" {
    fn checked_i8(value: Outer<i8>) -> Outer<i8>;
    fn checked_i16(value: Outer<i16>) -> Outer<i16>;
    fn checked_i32(value: Outer<i32>) -> Outer<i32>;
    fn checked_i64(value: Outer<i64>) -> Outer<i64>;
    fn checked_i128(value: Outer<i128>) -> Outer<i128>;
}
fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let mut checks = 0;
    macro_rules! check {
        ($name:ident, $ty:ty) => {
            if mode.starts_with(stringify!($ty)) {
                let v = if mode.ends_with("-hi") {
                    Pair {
                        hi: <$ty>::MIN,
                        lo: 1,
                    }
                } else {
                    Pair {
                        hi: 1,
                        lo: <$ty>::MIN,
                    }
                };
                std::hint::black_box(unsafe {
                    $name(Outer {
                        lead: 19,
                        inner: v,
                        tail: 0x792fa02865,
                    })
                });
                std::process::exit(77);
            }
            for hi in [0, 1, -1, <$ty>::MIN + 1, <$ty>::MAX] {
                let lo = hi / 2;
                let v = unsafe {
                    $name(Outer {
                        lead: 19,
                        inner: Pair { hi, lo },
                        tail: 0x792fa02865,
                    })
                };
                assert_eq!(v.lead, 19);
                assert_eq!(v.inner.hi, -hi);
                assert_eq!(v.inner.lo, -lo);
                assert_eq!(v.tail, 0x792fa02865);
                checks += 4;
            }
        };
    }
    check!(checked_i8, i8);
    check!(checked_i16, i16);
    check!(checked_i32, i32);
    check!(checked_i64, i64);
    check!(checked_i128, i128);
    assert!(mode.is_empty(), "unknown mode {mode}");
    println!("PASS memory_unary_checked checks={checks}");
}
