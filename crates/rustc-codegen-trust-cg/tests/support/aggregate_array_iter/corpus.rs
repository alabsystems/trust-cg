#![no_std]
mod types;
use types::*;

macro_rules! family {
    ($name:ident, $ty:ty, $v:ident, $bits:expr) => {
        mod $name {
            use super::*;
            #[inline(never)]
            fn consume<const N: usize>(values: [$ty; N], take: usize, reverse: bool) -> u64 {
                let mut iter = values.into_iter();
                let mut result = 0x917ac48de63250bfu64;
                let mut count = 0;
                while count < take {
                    let item = if reverse {
                        iter.next_back()
                    } else {
                        iter.next()
                    };
                    match item {
                        Some(value) => {
                            let $v = value;
                            let bits = $bits;
                            result = result.rotate_left(9) ^ bits;
                        }
                        None => break,
                    }
                    count += 1;
                }
                result ^ (count as u64)
            }
            macro_rules! export {
                ($fn:ident, $n:expr) => {
                    #[unsafe(export_name=concat!(stringify!($name), "_", stringify!($fn)))]
                    pub fn $fn(values: [$ty; $n], take: usize, reverse: bool) -> u64 {
                        // IntoIterator owns a copy. Its partial drop must not touch
                        // the caller's array, including when take is zero.
                        consume(values, take, reverse)
                    }
                };
            }
            export!(one, 1);
            export!(three, 3);
            export!(seven, 7);
        }
    };
}
family!(pair, Pair, v, v.0.to_bits() ^ v.1.to_bits().rotate_left(17));
family!(
    mixed,
    Mixed,
    v,
    u64::from(v.0) ^ u64::from(v.1.to_bits()).rotate_left(13) ^ v.2.rotate_left(37)
);
family!(
    padded,
    Padded,
    v,
    u64::from(v.first) ^ v.second.to_bits().rotate_left(19) ^ u64::from(v.third).rotate_left(41)
);
