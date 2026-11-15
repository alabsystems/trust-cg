#![no_std]
#![feature(core_intrinsics, const_eval_select)]
#![allow(internal_features)]
extern crate projected_aggregate_types;
use projected_aggregate_types::*;
macro_rules! cases {
    ($module:ident,$ty:ty,$selected:ident,$pressure:ident,$multiple:ident,$looped:ident,$mutated:ident,$tuple:ident) => {
        mod $module {
            use super::*;
            type Callback = fn($ty, u64) -> u64;
            type Pressure = fn(u64, u64, u64, u64, u64, u64, u64, $ty, u64) -> u64;
            const fn ct(_: u64, _v: $ty, _: Callback) -> u64 {
                0
            }
            #[inline(never)]
            fn rt(salt: u64, v: $ty, cb: Callback) -> u64 {
                cb(v, salt)
            }
            #[unsafe(no_mangle)]
            pub const fn $selected(v: $ty, salt: u64, cb: Callback) -> u64 {
                core::intrinsics::const_eval_select((salt, v, cb), ct, rt)
            }
            #[unsafe(no_mangle)]
            pub const fn $tuple(args: (u64, $ty, Callback)) -> u64 {
                core::intrinsics::const_eval_select(args, ct, rt)
            }
            const fn pc(
                _: u64,
                _: u64,
                _: u64,
                _: u64,
                _: u64,
                _: u64,
                _: u64,
                _v: $ty,
                _: u64,
                _: Pressure,
            ) -> u64 {
                0
            }
            #[inline(never)]
            fn pr(
                a: u64,
                b: u64,
                c: u64,
                d: u64,
                e: u64,
                f: u64,
                g: u64,
                v: $ty,
                salt: u64,
                cb: Pressure,
            ) -> u64 {
                cb(a, b, c, d, e, f, g, v, salt)
            }
            #[unsafe(no_mangle)]
            pub const fn $pressure(v: $ty, salt: u64, cb: Pressure) -> u64 {
                core::intrinsics::const_eval_select(
                    (11, 23, 37, 53, 71, 89, 107, v, salt, cb),
                    pc,
                    pr,
                )
            }
            const fn mc(_: u64, _a: $ty, _: $ty, _: fn($ty, $ty, u64) -> u64) -> u64 {
                0
            }
            #[inline(never)]
            fn mr(salt: u64, a: $ty, b: $ty, cb: fn($ty, $ty, u64) -> u64) -> u64 {
                cb(a, b, salt)
            }
            #[unsafe(no_mangle)]
            pub const fn $multiple(a: $ty, b: $ty, salt: u64, cb: fn($ty, $ty, u64) -> u64) -> u64 {
                core::intrinsics::const_eval_select((salt, a, b, cb), mc, mr)
            }
            #[unsafe(no_mangle)]
            pub fn $looped(v: $ty, salt: u64, cb: Callback) -> u64 {
                let mut result = 0;
                for _ in 0..3 {
                    result = $selected(v, salt, cb);
                }
                result
            }
        }
    };
}
cases!(
    layout,
    Layout,
    layout_selected,
    layout_pressure,
    layout_multiple,
    layout_looped,
    layout_mutated,
    layout_tuple
);
cases!(
    pair,
    Pair64,
    pair_selected,
    pair_pressure,
    pair_multiple,
    pair_looped,
    pair_mutated,
    pair_tuple
);
cases!(
    triple,
    Triple64,
    triple_selected,
    triple_pressure,
    triple_multiple,
    triple_looped,
    triple_mutated,
    triple_tuple
);
cases!(
    small,
    Small4,
    small_selected,
    small_pressure,
    small_multiple,
    small_looped,
    small_mutated,
    small_tuple
);
cases!(
    packed,
    Packed5,
    packed_selected,
    packed_pressure,
    packed_multiple,
    packed_looped,
    packed_mutated,
    packed_tuple
);
cases!(
    double,
    Float2,
    double_selected,
    double_pressure,
    double_multiple,
    double_looped,
    double_mutated,
    double_tuple
);
cases!(
    float,
    Float4,
    float_selected,
    float_pressure,
    float_multiple,
    float_looped,
    float_mutated,
    float_tuple
);
cases!(
    wide,
    WideRecord,
    wide_selected,
    wide_pressure,
    wide_multiple,
    wide_looped,
    wide_mutated,
    wide_tuple
);
cases!(
    choice,
    Choice,
    choice_selected,
    choice_pressure,
    choice_multiple,
    choice_looped,
    choice_mutated,
    choice_tuple
);
cases!(
    aligned,
    Aligned32,
    aligned_selected,
    aligned_pressure,
    aligned_multiple,
    aligned_looped,
    aligned_mutated,
    aligned_tuple
);
cases!(
    zst,
    WithZst,
    zst_selected,
    zst_pressure,
    zst_multiple,
    zst_looped,
    zst_mutated,
    zst_tuple
);
cases!(
    nested,
    Nested,
    nested_selected,
    nested_pressure,
    nested_multiple,
    nested_looped,
    nested_mutated,
    nested_tuple
);

type Flags = fn(Layout, bool, u64) -> u64;
const fn flags_const(_: Layout, _: bool, _: u64, _: Flags) -> u64 {
    0
}
#[inline(never)]
fn flags_runtime(v: Layout, flag: bool, salt: u64, cb: Flags) -> u64 {
    cb(v, flag, salt)
}
#[unsafe(no_mangle)]
pub const fn layout_flags(v: Layout, flag: bool, salt: u64, cb: Flags) -> u64 {
    core::intrinsics::const_eval_select((v, flag, salt, cb), flags_const, flags_runtime)
}
#[unsafe(no_mangle)]
pub fn layout_mutated(
    mut v: Layout,
    salt: u64,
    change: fn(&mut Layout, u64),
    cb: fn(Layout, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    layout::layout_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn pair_mutated(
    mut v: Pair64,
    salt: u64,
    change: fn(&mut Pair64, u64),
    cb: fn(Pair64, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    pair::pair_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn triple_mutated(
    mut v: Triple64,
    salt: u64,
    change: fn(&mut Triple64, u64),
    cb: fn(Triple64, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    triple::triple_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn small_mutated(
    mut v: Small4,
    salt: u64,
    change: fn(&mut Small4, u64),
    cb: fn(Small4, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    small::small_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn packed_mutated(
    mut v: Packed5,
    salt: u64,
    change: fn(&mut Packed5, u64),
    cb: fn(Packed5, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    packed::packed_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn double_mutated(
    mut v: Float2,
    salt: u64,
    change: fn(&mut Float2, u64),
    cb: fn(Float2, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    double::double_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn float_mutated(
    mut v: Float4,
    salt: u64,
    change: fn(&mut Float4, u64),
    cb: fn(Float4, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    float::float_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn wide_mutated(
    mut v: WideRecord,
    salt: u64,
    change: fn(&mut WideRecord, u64),
    cb: fn(WideRecord, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    wide::wide_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn choice_mutated(
    mut v: Choice,
    salt: u64,
    change: fn(&mut Choice, u64),
    cb: fn(Choice, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    choice::choice_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn aligned_mutated(
    mut v: Aligned32,
    salt: u64,
    change: fn(&mut Aligned32, u64),
    cb: fn(Aligned32, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    aligned::aligned_selected(v, salt, cb)
}
#[unsafe(no_mangle)]
pub fn nested_mutated(
    mut v: Nested,
    salt: u64,
    change: fn(&mut Nested, u64),
    cb: fn(Nested, u64) -> u64,
) -> u64 {
    change(&mut v, salt);
    nested::nested_selected(v, salt, cb)
}

#[unsafe(no_mangle)]
pub fn layout_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Layout,
    s: u64,
    cb: fn(Layout, u64) -> u64,
) -> u64 {
    layout::layout_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn pair_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Pair64,
    s: u64,
    cb: fn(Pair64, u64) -> u64,
) -> u64 {
    pair::pair_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn triple_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Triple64,
    s: u64,
    cb: fn(Triple64, u64) -> u64,
) -> u64 {
    triple::triple_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn small_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Small4,
    s: u64,
    cb: fn(Small4, u64) -> u64,
) -> u64 {
    small::small_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn packed_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Packed5,
    s: u64,
    cb: fn(Packed5, u64) -> u64,
) -> u64 {
    packed::packed_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn double_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Float2,
    s: u64,
    cb: fn(Float2, u64) -> u64,
) -> u64 {
    double::double_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn float_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Float4,
    s: u64,
    cb: fn(Float4, u64) -> u64,
) -> u64 {
    float::float_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn wide_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: WideRecord,
    s: u64,
    cb: fn(WideRecord, u64) -> u64,
) -> u64 {
    wide::wide_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn choice_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Choice,
    s: u64,
    cb: fn(Choice, u64) -> u64,
) -> u64 {
    choice::choice_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn aligned_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Aligned32,
    s: u64,
    cb: fn(Aligned32, u64) -> u64,
) -> u64 {
    aligned::aligned_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn zst_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: WithZst,
    s: u64,
    cb: fn(WithZst, u64) -> u64,
) -> u64 {
    zst::zst_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}

#[unsafe(no_mangle)]
pub fn nested_incoming(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    v: Nested,
    s: u64,
    cb: fn(Nested, u64) -> u64,
) -> u64 {
    nested::nested_selected(v, s, cb) ^ a ^ b ^ c ^ d ^ e ^ f ^ g
}
