mod types;
use types::*;
fn expected(bits: &[u64], take: usize, reverse: bool) -> u64 {
    let n = take.min(bits.len());
    let mut result = 0x917ac48de63250bfu64;
    for index in 0..n {
        let at = if reverse {
            bits.len() - index - 1
        } else {
            index
        };
        result = result.rotate_left(9) ^ bits[at];
    }
    result ^ n as u64
}
macro_rules! declarations {
    ($name:ident, $ty:ty) => {
        mod $name {
            use super::*;
            unsafe extern "Rust" {
                #[link_name=concat!(stringify!($name),"_one")]
                pub fn one(values: [$ty; 1], take: usize, reverse: bool) -> u64;
                #[link_name=concat!(stringify!($name),"_three")]
                pub fn three(values: [$ty; 3], take: usize, reverse: bool) -> u64;
                #[link_name=concat!(stringify!($name),"_seven")]
                pub fn seven(values: [$ty; 7], take: usize, reverse: bool) -> u64;
            }
        }
    };
}
declarations!(pair, Pair);
declarations!(mixed, Mixed);
declarations!(padded, Padded);
fn random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}
fn main() {
    let mut checks = 0;
    let mut state = 0x425ead937681b0cfu64;
    for seed in 0..128 {
        macro_rules! case {
            ($fn:ident, $n:expr) => {{
                let pairs: [Pair; $n] = core::array::from_fn(|i| {
                    let a = match (seed + i) % 8 {
                        0 => 0,
                        1 => 1 << 63,
                        2 => 0x7ff0000000000000,
                        3 => 0x7ff8123456789abc,
                        4 => 0xffffffffffffffff,
                        _ => random(&mut state),
                    };
                    (f64::from_bits(a), f64::from_bits(random(&mut state)))
                });
                let mixed: [Mixed; $n] = core::array::from_fn(|_| {
                    (
                        random(&mut state) as u8,
                        f32::from_bits(random(&mut state) as u32),
                        random(&mut state),
                    )
                });
                let padded: [Padded; $n] = core::array::from_fn(|_| Padded {
                    first: random(&mut state) as u8,
                    second: f64::from_bits(random(&mut state)),
                    third: random(&mut state) as u16,
                });
                let pbits: [u64; $n] = pairs.map(|v| v.0.to_bits() ^ v.1.to_bits().rotate_left(17));
                let mbits: [u64; $n] = mixed.map(|v| {
                    u64::from(v.0) ^ u64::from(v.1.to_bits()).rotate_left(13) ^ v.2.rotate_left(37)
                });
                let sbits: [u64; $n] = padded.map(|v| {
                    u64::from(v.first)
                        ^ v.second.to_bits().rotate_left(19)
                        ^ u64::from(v.third).rotate_left(41)
                });
                for take in 0..=$n + 1 {
                    for reverse in [false, true] {
                        unsafe {
                            assert_eq!(
                                pair::$fn(pairs, take, reverse),
                                expected(&pbits, take, reverse),
                                "pair seed={seed} n={} take={take} reverse={reverse}",
                                $n
                            );
                            assert_eq!(
                                mixed::$fn(mixed, take, reverse),
                                expected(&mbits, take, reverse),
                                "mixed seed={seed} n={} take={take} reverse={reverse}",
                                $n
                            );
                            assert_eq!(
                                padded::$fn(padded, take, reverse),
                                expected(&sbits, take, reverse),
                                "padded seed={seed} n={} take={take} reverse={reverse}",
                                $n
                            );
                        }
                        checks += 3;
                    }
                }
            }};
        }
        case!(one, 1);
        case!(three, 3);
        case!(seven, 7);
    }
    println!("PASS aggregate_array_iter checks={checks}");
}
