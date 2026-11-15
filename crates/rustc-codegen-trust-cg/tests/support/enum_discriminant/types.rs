#![allow(dead_code)]
macro_rules! enumeration {
    ($name:ident, $repr:ident, $a:expr, $b:expr, $c:expr, $d:expr) => {
        pub mod $name {
            #[repr($repr)]
            #[derive(Clone, Copy, PartialEq, Eq)]
            pub enum E {
                A = $a,
                B = $b,
                C = $c,
                D = $d,
            }
            pub const VALUES: [E; 4] = [E::A, E::B, E::C, E::D];
            pub const TAGS: [i128; 4] = [$a as i128, $b as i128, $c as i128, $d as i128];
        }
    };
}
enumeration!(signed8, i8, -128, -1, 0, 127);
enumeration!(unsigned8, u8, 0, 1, 129, 255);
enumeration!(signed16, i16, -32768, -7, 13, 32767);
enumeration!(unsigned16, u16, 0, 257, 32769, 65535);
enumeration!(signed32, i32, i32::MIN, -19, 65537, i32::MAX);
enumeration!(unsigned32, u32, 0, 65539, 0x80000001, u32::MAX);
enumeration!(signed64, i64, i64::MIN, -29, 0x100000001, i64::MAX);
enumeration!(
    unsigned64,
    u64,
    0,
    0x100000003,
    0x8000000000000001u64,
    u64::MAX
);
enumeration!(signed128, i128, i128::MIN, -37, 1i128 << 100, i128::MAX);
enumeration!(
    unsigned128,
    u128,
    0,
    1u128 << 65,
    (1u128 << 127) + 3,
    u128::MAX
);
pub mod inferred {
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum E {
        A,
        B,
        C,
        D,
    }
    pub const VALUES: [E; 4] = [E::A, E::B, E::C, E::D];
    pub const TAGS: [i128; 4] = [0, 1, 2, 3];
}
pub mod ordering {
    pub use core::cmp::Ordering as E;
    pub const VALUES: [E; 4] = [E::Less, E::Equal, E::Greater, E::Less];
    pub const TAGS: [i128; 4] = [-1, 0, 1, -1];
}
