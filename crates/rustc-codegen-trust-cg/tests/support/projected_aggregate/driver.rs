extern crate projected_aggregate_types;
use projected_aggregate_types::*;
use std::sync::atomic::{AtomicUsize, Ordering};
const MASK: u64 = 0xa579_13be_d264_80fc;
const SECOND: u64 = 0x1c75_be9a_283d_460f;
static CHECKS: AtomicUsize = AtomicUsize::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
fn check(v: bool) {
    assert!(v, "check {} failed", CHECKS.load(Ordering::Relaxed));
    CHECKS.fetch_add(1, Ordering::Relaxed);
}
fn word(x: u64) -> u64 {
    x.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x1234_5678_abcd_ef01
}
trait Model: Copy {
    fn make(s: u64) -> Self;
    fn same(&self, v: &Self) -> bool;
}
macro_rules! model {
    ($ty:ty,$s:ident,$body:expr) => {
        impl Model for $ty {
            fn make($s: u64) -> Self {
                $body
            }
            fn same(&self, v: &Self) -> bool {
                self == v
            }
        }
    };
}
model!(
    Layout,
    s,
    Layout::from_size_align((s as usize) & 0xffff, 1 << ((s >> 16) % 13)).unwrap()
);
model!(
    Pair64,
    s,
    Pair64 {
        a: word(s),
        b: word(s ^ MASK)
    }
);
model!(
    Triple64,
    s,
    Triple64 {
        a: word(s),
        b: word(s ^ MASK),
        c: word(s ^ SECOND)
    }
);
model!(
    Small4,
    s,
    Small4 {
        a: s as u16,
        b: (s >> 16) as u16
    }
);
model!(
    Choice,
    s,
    if s & 1 == 0 {
        Choice::Small {
            a: word(s),
            b: (s >> 32) as u8,
        }
    } else {
        Choice::Large {
            a: word(s),
            b: word(s ^ MASK),
            c: word(s ^ SECOND),
        }
    }
);
impl Model for Aligned32 {
    fn make(s: u64) -> Self {
        Self {
            a: ((word(s) as u128) << 64) | word(s ^ MASK) as u128,
            b: word(s ^ SECOND),
        }
    }
    fn same(&self, v: &Self) -> bool {
        if self != v {
            eprintln!(
                "Aligned32 got ({:#x},{:#x}), expected ({:#x},{:#x})",
                self.a, self.b, v.a, v.b
            );
        }
        self == v
    }
}
impl Model for WithZst {
    fn make(s: u64) -> Self {
        Self {
            z: (),
            a: word(s),
            marker: (),
            b: (s >> 40) as u16,
        }
    }
    fn same(&self, v: &Self) -> bool {
        if self != v {
            eprintln!(
                "WithZst got ({:#x},{:#x}), expected ({:#x},{:#x})",
                self.a, self.b, v.a, v.b
            );
        }
        self == v
    }
}
model!(
    Nested,
    s,
    Nested {
        z: (),
        a: Small4::make(s),
        b: Pair64::make(s ^ SECOND),
        c: (s >> 32) as u8
    }
);
impl Model for Packed5 {
    fn make(s: u64) -> Self {
        Self {
            a: s as u8,
            b: (s >> 24) as u32,
        }
    }
    fn same(&self, v: &Self) -> bool {
        self.a == v.a && self.b == v.b
    }
}
impl Model for Float2 {
    fn make(s: u64) -> Self {
        Self {
            a: f64::from_bits(word(s)),
            b: f64::from_bits(word(s ^ MASK)),
        }
    }
    fn same(&self, v: &Self) -> bool {
        self.a.to_bits() == v.a.to_bits() && self.b.to_bits() == v.b.to_bits()
    }
}
impl Model for Float4 {
    fn make(s: u64) -> Self {
        Self {
            a: f32::from_bits(s as u32),
            b: f32::from_bits((s >> 32) as u32),
            c: f32::from_bits(word(s) as u32),
            d: f32::from_bits(word(s ^ MASK) as u32),
        }
    }
    fn same(&self, v: &Self) -> bool {
        self.a.to_bits() == v.a.to_bits()
            && self.b.to_bits() == v.b.to_bits()
            && self.c.to_bits() == v.c.to_bits()
            && self.d.to_bits() == v.d.to_bits()
    }
}
impl Model for WideRecord {
    fn make(s: u64) -> Self {
        const DATA: &[u8] = b"distinct pointer metadata across aggregate arguments";
        Self {
            head: word(s),
            bytes: &DATA[(s as usize) % 8..8 + (s as usize) % 41],
            tail: (s >> 40) as u16,
        }
    }
    fn same(&self, v: &Self) -> bool {
        self.head == v.head
            && self.tail == v.tail
            && self.bytes.as_ptr() == v.bytes.as_ptr()
            && self.bytes.len() == v.bytes.len()
            && self.bytes == v.bytes
    }
}
impl Model for Union24 {
    fn make(s: u64) -> Self {
        Self {
            words: [word(s), word(s ^ MASK), word(s ^ SECOND)],
        }
    }
    fn same(&self, v: &Self) -> bool {
        unsafe { self.words == v.words }
    }
}
#[allow(improper_ctypes)]
unsafe extern "Rust" {
    fn layout_incoming(
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
    ) -> u64;
    fn pair_incoming(
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
    ) -> u64;
    fn triple_incoming(
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
    ) -> u64;
    fn small_incoming(
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
    ) -> u64;
    fn packed_incoming(
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
    ) -> u64;
    fn double_incoming(
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
    ) -> u64;
    fn float_incoming(
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
    ) -> u64;
    fn wide_incoming(
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
    ) -> u64;
    fn choice_incoming(
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
    ) -> u64;
    fn aligned_incoming(
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
    ) -> u64;
    fn zst_incoming(
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
    ) -> u64;
    fn nested_incoming(
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
    ) -> u64;
    fn layout_selected(v: Layout, s: u64, cb: fn(Layout, u64) -> u64) -> u64;
    fn layout_tuple(v: (u64, Layout, fn(Layout, u64) -> u64)) -> u64;
    fn layout_pressure(
        v: Layout,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Layout, u64) -> u64,
    ) -> u64;
    fn layout_multiple(a: Layout, b: Layout, s: u64, cb: fn(Layout, Layout, u64) -> u64) -> u64;
    fn layout_looped(v: Layout, s: u64, cb: fn(Layout, u64) -> u64) -> u64;
    fn layout_mutated(
        v: Layout,
        s: u64,
        change: fn(&mut Layout, u64),
        cb: fn(Layout, u64) -> u64,
    ) -> u64;
    fn nested_selected(v: Nested, s: u64, cb: fn(Nested, u64) -> u64) -> u64;
    fn nested_tuple(v: (u64, Nested, fn(Nested, u64) -> u64)) -> u64;
    fn nested_pressure(
        v: Nested,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Nested, u64) -> u64,
    ) -> u64;
    fn nested_multiple(a: Nested, b: Nested, s: u64, cb: fn(Nested, Nested, u64) -> u64) -> u64;
    fn nested_looped(v: Nested, s: u64, cb: fn(Nested, u64) -> u64) -> u64;
    fn nested_mutated(
        v: Nested,
        s: u64,
        change: fn(&mut Nested, u64),
        cb: fn(Nested, u64) -> u64,
    ) -> u64;
    fn zst_selected(v: WithZst, s: u64, cb: fn(WithZst, u64) -> u64) -> u64;
    fn zst_tuple(v: (u64, WithZst, fn(WithZst, u64) -> u64)) -> u64;
    fn zst_pressure(
        v: WithZst,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, WithZst, u64) -> u64,
    ) -> u64;
    fn zst_multiple(a: WithZst, b: WithZst, s: u64, cb: fn(WithZst, WithZst, u64) -> u64) -> u64;
    fn zst_looped(v: WithZst, s: u64, cb: fn(WithZst, u64) -> u64) -> u64;

    fn pair_selected(v: Pair64, s: u64, cb: fn(Pair64, u64) -> u64) -> u64;
    fn pair_tuple(v: (u64, Pair64, fn(Pair64, u64) -> u64)) -> u64;
    fn pair_pressure(
        v: Pair64,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Pair64, u64) -> u64,
    ) -> u64;
    fn pair_multiple(a: Pair64, b: Pair64, s: u64, cb: fn(Pair64, Pair64, u64) -> u64) -> u64;
    fn pair_looped(v: Pair64, s: u64, cb: fn(Pair64, u64) -> u64) -> u64;
    fn pair_mutated(
        v: Pair64,
        s: u64,
        change: fn(&mut Pair64, u64),
        cb: fn(Pair64, u64) -> u64,
    ) -> u64;
    fn triple_selected(v: Triple64, s: u64, cb: fn(Triple64, u64) -> u64) -> u64;
    fn triple_tuple(v: (u64, Triple64, fn(Triple64, u64) -> u64)) -> u64;
    fn triple_pressure(
        v: Triple64,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Triple64, u64) -> u64,
    ) -> u64;
    fn triple_multiple(
        a: Triple64,
        b: Triple64,
        s: u64,
        cb: fn(Triple64, Triple64, u64) -> u64,
    ) -> u64;
    fn triple_looped(v: Triple64, s: u64, cb: fn(Triple64, u64) -> u64) -> u64;
    fn triple_mutated(
        v: Triple64,
        s: u64,
        change: fn(&mut Triple64, u64),
        cb: fn(Triple64, u64) -> u64,
    ) -> u64;
    fn small_selected(v: Small4, s: u64, cb: fn(Small4, u64) -> u64) -> u64;
    fn small_tuple(v: (u64, Small4, fn(Small4, u64) -> u64)) -> u64;
    fn small_pressure(
        v: Small4,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Small4, u64) -> u64,
    ) -> u64;
    fn small_multiple(a: Small4, b: Small4, s: u64, cb: fn(Small4, Small4, u64) -> u64) -> u64;
    fn small_looped(v: Small4, s: u64, cb: fn(Small4, u64) -> u64) -> u64;
    fn small_mutated(
        v: Small4,
        s: u64,
        change: fn(&mut Small4, u64),
        cb: fn(Small4, u64) -> u64,
    ) -> u64;
    fn packed_selected(v: Packed5, s: u64, cb: fn(Packed5, u64) -> u64) -> u64;
    fn packed_tuple(v: (u64, Packed5, fn(Packed5, u64) -> u64)) -> u64;
    fn packed_pressure(
        v: Packed5,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Packed5, u64) -> u64,
    ) -> u64;
    fn packed_multiple(a: Packed5, b: Packed5, s: u64, cb: fn(Packed5, Packed5, u64) -> u64)
    -> u64;
    fn packed_looped(v: Packed5, s: u64, cb: fn(Packed5, u64) -> u64) -> u64;
    fn packed_mutated(
        v: Packed5,
        s: u64,
        change: fn(&mut Packed5, u64),
        cb: fn(Packed5, u64) -> u64,
    ) -> u64;
    fn double_selected(v: Float2, s: u64, cb: fn(Float2, u64) -> u64) -> u64;
    fn double_tuple(v: (u64, Float2, fn(Float2, u64) -> u64)) -> u64;
    fn double_pressure(
        v: Float2,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Float2, u64) -> u64,
    ) -> u64;
    fn double_multiple(a: Float2, b: Float2, s: u64, cb: fn(Float2, Float2, u64) -> u64) -> u64;
    fn double_looped(v: Float2, s: u64, cb: fn(Float2, u64) -> u64) -> u64;
    fn double_mutated(
        v: Float2,
        s: u64,
        change: fn(&mut Float2, u64),
        cb: fn(Float2, u64) -> u64,
    ) -> u64;
    fn float_selected(v: Float4, s: u64, cb: fn(Float4, u64) -> u64) -> u64;
    fn float_tuple(v: (u64, Float4, fn(Float4, u64) -> u64)) -> u64;
    fn float_pressure(
        v: Float4,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Float4, u64) -> u64,
    ) -> u64;
    fn float_multiple(a: Float4, b: Float4, s: u64, cb: fn(Float4, Float4, u64) -> u64) -> u64;
    fn float_looped(v: Float4, s: u64, cb: fn(Float4, u64) -> u64) -> u64;
    fn float_mutated(
        v: Float4,
        s: u64,
        change: fn(&mut Float4, u64),
        cb: fn(Float4, u64) -> u64,
    ) -> u64;
    fn wide_selected(v: WideRecord, s: u64, cb: fn(WideRecord, u64) -> u64) -> u64;
    fn wide_tuple(v: (u64, WideRecord, fn(WideRecord, u64) -> u64)) -> u64;
    fn wide_pressure(
        v: WideRecord,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, WideRecord, u64) -> u64,
    ) -> u64;
    fn wide_multiple(
        a: WideRecord,
        b: WideRecord,
        s: u64,
        cb: fn(WideRecord, WideRecord, u64) -> u64,
    ) -> u64;
    fn wide_looped(v: WideRecord, s: u64, cb: fn(WideRecord, u64) -> u64) -> u64;
    fn wide_mutated(
        v: WideRecord,
        s: u64,
        change: fn(&mut WideRecord, u64),
        cb: fn(WideRecord, u64) -> u64,
    ) -> u64;
    fn choice_selected(v: Choice, s: u64, cb: fn(Choice, u64) -> u64) -> u64;
    fn choice_tuple(v: (u64, Choice, fn(Choice, u64) -> u64)) -> u64;
    fn choice_pressure(
        v: Choice,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Choice, u64) -> u64,
    ) -> u64;
    fn choice_multiple(a: Choice, b: Choice, s: u64, cb: fn(Choice, Choice, u64) -> u64) -> u64;
    fn choice_looped(v: Choice, s: u64, cb: fn(Choice, u64) -> u64) -> u64;
    fn choice_mutated(
        v: Choice,
        s: u64,
        change: fn(&mut Choice, u64),
        cb: fn(Choice, u64) -> u64,
    ) -> u64;
    fn aligned_selected(v: Aligned32, s: u64, cb: fn(Aligned32, u64) -> u64) -> u64;
    fn aligned_tuple(v: (u64, Aligned32, fn(Aligned32, u64) -> u64)) -> u64;
    fn aligned_pressure(
        v: Aligned32,
        s: u64,
        cb: fn(u64, u64, u64, u64, u64, u64, u64, Aligned32, u64) -> u64,
    ) -> u64;
    fn aligned_multiple(
        a: Aligned32,
        b: Aligned32,
        s: u64,
        cb: fn(Aligned32, Aligned32, u64) -> u64,
    ) -> u64;
    fn aligned_looped(v: Aligned32, s: u64, cb: fn(Aligned32, u64) -> u64) -> u64;
    fn aligned_mutated(
        v: Aligned32,
        s: u64,
        change: fn(&mut Aligned32, u64),
        cb: fn(Aligned32, u64) -> u64,
    ) -> u64;

}
fn flags_callback(v: Layout, flag: bool, salt: u64) -> u64 {
    check(v.same(&Layout::make(salt)));
    check(flag == (salt & 1 != 0));
    word(salt ^ MASK)
}
unsafe extern "Rust" {
    fn layout_flags(v: Layout, flag: bool, salt: u64, cb: fn(Layout, bool, u64) -> u64) -> u64;
}
fn callback<T: Model>(v: T, s: u64) -> u64 {
    check(v.same(&T::make(s)));
    CALLS.fetch_add(1, Ordering::Relaxed);
    word(s ^ MASK)
}
fn pressure<T: Model>(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, v: T, s: u64) -> u64 {
    for (x, y) in [a, b, c, d, e, f, g]
        .into_iter()
        .zip([11, 23, 37, 53, 71, 89, 107])
    {
        check(x == y);
    }
    callback(v, s)
}
fn multiple<T: Model>(a: T, b: T, s: u64) -> u64 {
    check(a.same(&T::make(s)));
    check(b.same(&T::make(s ^ SECOND)));
    CALLS.fetch_add(1, Ordering::Relaxed);
    word(s ^ MASK)
}
fn change<T: Model>(v: &mut T, s: u64) {
    check(v.same(&T::make(!s)));
    *v = T::make(s);
    CALLS.fetch_add(1, Ordering::Relaxed);
}
fn reset() {
    CALLS.store(0, Ordering::Relaxed);
}
fn result(v: u64, s: u64, calls: usize) {
    check(v == word(s ^ MASK));
    check(CALLS.load(Ordering::Relaxed) == calls);
}
#[allow(clippy::type_complexity)]
fn run<T: Model>(
    selected: unsafe fn(T, u64, fn(T, u64) -> u64) -> u64,
    stack: unsafe fn(T, u64, fn(u64, u64, u64, u64, u64, u64, u64, T, u64) -> u64) -> u64,
    multi: unsafe fn(T, T, u64, fn(T, T, u64) -> u64) -> u64,
    looped: unsafe fn(T, u64, fn(T, u64) -> u64) -> u64,
    mutated: Option<unsafe fn(T, u64, fn(&mut T, u64), fn(T, u64) -> u64) -> u64>,
    tuple: unsafe fn((u64, T, fn(T, u64) -> u64)) -> u64,
    incoming: unsafe fn(u64, u64, u64, u64, u64, u64, u64, T, u64, fn(T, u64) -> u64) -> u64,
) {
    for i in 0..=257 {
        let s = word(i);
        unsafe {
            reset();
            result(selected(T::make(s), s, callback::<T>), s, 1);
            reset();
            result(stack(T::make(s), s, pressure::<T>), s, 1);
            reset();
            result(
                multi(T::make(s), T::make(s ^ SECOND), s, multiple::<T>),
                s,
                1,
            );
            reset();
            result(looped(T::make(s), s, callback::<T>), s, 3);
            if let Some(mutated) = mutated {
                reset();
                result(mutated(T::make(!s), s, change::<T>, callback::<T>), s, 2);
            }
            reset();
            result(tuple((s, T::make(s), callback::<T>)), s, 1);
            reset();
            result(
                incoming(11, 23, 37, 53, 71, 89, 107, T::make(s), s, callback::<T>)
                    ^ (11 ^ 23 ^ 37 ^ 53 ^ 71 ^ 89 ^ 107),
                s,
                1,
            );
        }
    }
}
fn main() {
    for i in 0..516 {
        let s = word(i);
        check(
            unsafe { layout_flags(Layout::make(s), s & 1 != 0, s, flags_callback) }
                == word(s ^ MASK),
        );
    }
    run::<WithZst>(
        zst_selected,
        zst_pressure,
        zst_multiple,
        zst_looped,
        None,
        zst_tuple,
        zst_incoming,
    );
    run::<Nested>(
        nested_selected,
        nested_pressure,
        nested_multiple,
        nested_looped,
        Some(nested_mutated),
        nested_tuple,
        nested_incoming,
    );

    run::<Layout>(
        layout_selected,
        layout_pressure,
        layout_multiple,
        layout_looped,
        Some(layout_mutated),
        layout_tuple,
        layout_incoming,
    );
    run::<Pair64>(
        pair_selected,
        pair_pressure,
        pair_multiple,
        pair_looped,
        Some(pair_mutated),
        pair_tuple,
        pair_incoming,
    );
    run::<Triple64>(
        triple_selected,
        triple_pressure,
        triple_multiple,
        triple_looped,
        Some(triple_mutated),
        triple_tuple,
        triple_incoming,
    );
    run::<Small4>(
        small_selected,
        small_pressure,
        small_multiple,
        small_looped,
        Some(small_mutated),
        small_tuple,
        small_incoming,
    );
    run::<Packed5>(
        packed_selected,
        packed_pressure,
        packed_multiple,
        packed_looped,
        Some(packed_mutated),
        packed_tuple,
        packed_incoming,
    );
    run::<Float2>(
        double_selected,
        double_pressure,
        double_multiple,
        double_looped,
        Some(double_mutated),
        double_tuple,
        double_incoming,
    );
    run::<Float4>(
        float_selected,
        float_pressure,
        float_multiple,
        float_looped,
        Some(float_mutated),
        float_tuple,
        float_incoming,
    );
    run::<WideRecord>(
        wide_selected,
        wide_pressure,
        wide_multiple,
        wide_looped,
        Some(wide_mutated),
        wide_tuple,
        wide_incoming,
    );
    run::<Choice>(
        choice_selected,
        choice_pressure,
        choice_multiple,
        choice_looped,
        Some(choice_mutated),
        choice_tuple,
        choice_incoming,
    );
    run::<Aligned32>(
        aligned_selected,
        aligned_pressure,
        aligned_multiple,
        aligned_looped,
        Some(aligned_mutated),
        aligned_tuple,
        aligned_incoming,
    );

    println!(
        "PASS projected_aggregate checks={}",
        CHECKS.load(Ordering::Relaxed)
    );
}
