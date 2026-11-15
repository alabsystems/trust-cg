#![no_std]
mod types;
macro_rules! operations {
    ($name:ident) => {
        mod $name {
            use super::types::$name::{E, VALUES};
            unsafe extern "Rust" {
                #[link_name=concat!(stringify!($name),"_observe")]
                fn observe(value: &E) -> i128;
                #[link_name=concat!(stringify!($name),"_replace")]
                fn replace(value: &mut E, next: E);
            }
            #[unsafe(export_name=concat!(stringify!($name),"_shared"))]
            pub fn shared(value: E) -> i128 {
                let before = value as i128;
                let observed = unsafe { observe(&value) };
                before.rotate_left(7)
                    ^ observed
                    ^ (value as i128).rotate_left(31)
                    ^ i128::from(value != VALUES[1])
            }
            #[unsafe(export_name=concat!(stringify!($name),"_mutated"))]
            pub fn mutated(mut value: E, next: E) -> i128 {
                let before = value as i128;
                unsafe { replace(&mut value, next) };
                before ^ (value as i128).rotate_left(27)
            }
            #[unsafe(export_name=concat!(stringify!($name),"_reassigned"))]
            pub fn reassigned(value: E, next: E, choose: bool) -> i128 {
                let mut local = if choose { value } else { next };
                unsafe { replace(&mut local, VALUES[2]) };
                let changed = local as i128;
                local = if choose { VALUES[3] } else { value };
                changed ^ unsafe { observe(&local) }.rotate_left(9) ^ (local as i128)
            }
            #[unsafe(export_name=concat!(stringify!($name),"_raw"))]
            pub fn raw(mut value: E, next: E) -> i128 {
                let p = &raw mut value;
                unsafe {
                    *p = next;
                }
                (value as i128) ^ unsafe { observe(&value) }.rotate_left(11)
            }
            #[unsafe(export_name=concat!(stringify!($name),"_branch"))]
            pub fn branch(mut left: E, mut right: E, choose: bool) -> i128 {
                let p = if choose { &mut left } else { &mut right };
                unsafe { replace(p, VALUES[2]) };
                (left as i128) ^ (right as i128).rotate_left(47)
            }
            #[unsafe(export_name=concat!(stringify!($name),"_looped"))]
            pub fn looped(mut value: E, next: E, count: u32) -> i128 {
                let mut i = 0;
                let mut result = value as i128;
                while i < count {
                    unsafe { replace(&mut value, next) };
                    result = result.rotate_left(5) ^ (value as i128);
                    value = VALUES[3];
                    result ^= unsafe { observe(&value) };
                    i += 1;
                }
                result ^ value as i128
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

mod literals {
    macro_rules! construct {
        ($name:ident, $a:ident, $b:ident, $c:ident, $d:ident) => {
            #[unsafe(export_name=concat!("literal_", stringify!($name)))]
            pub fn $name(index: u8) -> i128 {
                use super::types::$name::E;
                unsafe extern "Rust" {
                    #[link_name=concat!(stringify!($name), "_observe")]
                    fn observe(value: &E) -> i128;
                }
                let mut value = match index {
                    0 => E::$a,
                    1 => E::$b,
                    2 => E::$c,
                    _ => E::$d,
                };
                let before = unsafe { observe(&value) };
                value = match (index + 1) % 4 {
                    0 => E::$a,
                    1 => E::$b,
                    2 => E::$c,
                    _ => E::$d,
                };
                before ^ unsafe { observe(&value) }.rotate_left(19) ^ value as i128
            }
        };
    }
    construct!(signed8, A, B, C, D);
    construct!(inferred, A, B, C, D);
    construct!(ordering, Less, Equal, Greater, Less);
}
