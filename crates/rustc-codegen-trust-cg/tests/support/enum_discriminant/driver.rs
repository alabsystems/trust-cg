mod types;
macro_rules! operations {
    ($name:ident) => {
        mod $name {
            use super::types::$name::{E, TAGS, VALUES};
            unsafe extern "Rust" {
                #[link_name=concat!(stringify!($name),"_shared")]
                fn shared(v: E) -> i128;
                #[link_name=concat!(stringify!($name),"_mutated")]
                fn mutated(v: E, n: E) -> i128;
                #[link_name=concat!(stringify!($name),"_reassigned")]
                fn reassigned(v: E, n: E, b: bool) -> i128;
                #[link_name=concat!(stringify!($name),"_raw")]
                fn raw(v: E, n: E) -> i128;
                #[link_name=concat!(stringify!($name),"_branch")]
                fn branch(v: E, n: E, b: bool) -> i128;
                #[link_name=concat!(stringify!($name),"_looped")]
                fn looped(v: E, n: E, count: u32) -> i128;
            }
            #[unsafe(export_name=concat!(stringify!($name),"_observe"))]
            fn observe(value: &E) -> i128 {
                *value as i128
            }
            #[unsafe(export_name=concat!(stringify!($name),"_replace"))]
            fn replace(value: &mut E, next: E) {
                *value = next;
            }
            pub fn test() -> u64 {
                let mut checks = 0;
                for i in 0..4 {
                    for j in 0..4 {
                        for choose in [false, true] {
                            let a = TAGS[i];
                            let b = TAGS[j];
                            assert_eq!(
                                unsafe { shared(VALUES[i]) },
                                a.rotate_left(7) ^ a ^ a.rotate_left(31) ^ i128::from(a != TAGS[1]),
                                "{} shared {i}",
                                stringify!($name)
                            );
                            assert_eq!(
                                unsafe { mutated(VALUES[i], VALUES[j]) },
                                a ^ b.rotate_left(27),
                                "{} mutated {i}/{j}",
                                stringify!($name)
                            );
                            let v = if choose { TAGS[3] } else { a };
                            assert_eq!(
                                unsafe { reassigned(VALUES[i], VALUES[j], choose) },
                                TAGS[2] ^ v.rotate_left(9) ^ v,
                                "{} reassigned",
                                stringify!($name)
                            );
                            assert_eq!(
                                unsafe { raw(VALUES[i], VALUES[j]) },
                                b ^ b.rotate_left(11),
                                "{} raw",
                                stringify!($name)
                            );
                            let (l, r) = if choose { (TAGS[2], b) } else { (a, TAGS[2]) };
                            assert_eq!(
                                unsafe { branch(VALUES[i], VALUES[j], choose) },
                                l ^ r.rotate_left(47),
                                "{} branch",
                                stringify!($name)
                            );
                            checks += 5;
                            for count in 0..8 {
                                let mut result = a;
                                for _ in 0..count {
                                    result = result.rotate_left(5) ^ b ^ TAGS[3];
                                }
                                result ^= if count == 0 { a } else { TAGS[3] };
                                assert_eq!(
                                    unsafe { looped(VALUES[i], VALUES[j], count) },
                                    result,
                                    "{} loop {count}",
                                    stringify!($name)
                                );
                                checks += 1;
                            }
                        }
                    }
                }
                checks
            }
        }
    };
}
operations!(signed8);
operations!(unsigned8);
operations!(signed16);
operations!(unsigned16);
operations!(signed32);
operations!(unsigned32);
operations!(signed64);
operations!(unsigned64);
operations!(signed128);
operations!(unsigned128);
operations!(inferred);
operations!(ordering);
fn main() {
    let mut checks = signed8::test()
        + unsigned8::test()
        + signed16::test()
        + unsigned16::test()
        + signed32::test()
        + unsigned32::test()
        + signed64::test()
        + unsigned64::test()
        + signed128::test()
        + unsigned128::test()
        + inferred::test()
        + ordering::test();
    macro_rules! literal {
        ($name:ident) => {{
            unsafe extern "Rust" {
                #[link_name=concat!("literal_", stringify!($name))]
                fn literal(index: u8) -> i128;
            }
            let tags = types::$name::TAGS;
            for i in 0..4 {
                let before = tags[i];
                let after = tags[(i + 1) % 4];
                assert_eq!(
                    unsafe { literal(i as u8) },
                    before ^ after.rotate_left(19) ^ after
                );
                checks += 1;
            }
        }};
    }
    literal!(signed8);
    literal!(inferred);
    literal!(ordering);
    println!("PASS enum_discriminant checks={checks}");
}
