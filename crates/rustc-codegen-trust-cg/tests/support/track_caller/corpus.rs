#![no_std]
use core::panic::Location;

pub const LEAF_LINE: u32 = line!() + 3;
#[track_caller]
#[inline(never)]
pub fn leaf() -> &'static Location<'static> {
    Location::caller()
}

#[track_caller]
#[inline(never)]
pub fn chain() -> &'static Location<'static> {
    leaf()
}

#[track_caller]
#[inline(always)]
fn inline_leaf() -> &'static Location<'static> {
    Location::caller()
}

#[track_caller]
#[inline(never)]
pub fn through_inline() -> &'static Location<'static> {
    inline_leaf()
}

#[track_caller]
#[inline(never)]
pub fn recursive(n: u32) -> &'static Location<'static> {
    if n == 0 { leaf() } else { recursive(n - 1) }
}

pub const BOUNDARY_LINE: u32 = line!() + 3;
#[inline(never)]
pub fn boundary() -> &'static Location<'static> {
    leaf()
}

pub const INLINE_BOUNDARY_LINE: u32 = line!() + 3;
#[inline(always)]
fn inline_boundary() -> &'static Location<'static> {
    leaf()
}

#[track_caller]
#[inline(never)]
pub fn through_boundary() -> &'static Location<'static> {
    inline_boundary()
}

#[track_caller]
#[inline(never)]
pub fn many(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
    i: u64,
    j: u64,
) -> (&'static Location<'static>, u64) {
    (
        leaf(),
        a ^ b.rotate_left(1)
            ^ c.rotate_left(2)
            ^ d.rotate_left(3)
            ^ e.rotate_left(4)
            ^ f.rotate_left(5)
            ^ g.rotate_left(6)
            ^ h.rotate_left(7)
            ^ i.rotate_left(8)
            ^ j.rotate_left(9),
    )
}

#[track_caller]
#[inline(never)]
pub fn buffered(x: u64) -> ([u64; 4], &'static Location<'static>) {
    (
        [x, x.wrapping_add(1), x.wrapping_add(2), x.wrapping_add(3)],
        leaf(),
    )
}

#[inline(never)]
pub fn reify() -> fn() -> &'static Location<'static> {
    leaf
}

pub trait Tracked {
    #[track_caller]
    fn locate(&self) -> &'static Location<'static>;
}
pub struct Marker;
impl Tracked for Marker {
    #[inline(never)]
    fn locate(&self) -> &'static Location<'static> {
        leaf()
    }
}
#[track_caller]
#[inline(never)]
pub fn dynamic(obj: &dyn Tracked) -> &'static Location<'static> {
    obj.locate()
}

#[track_caller]
#[inline(never)]
pub fn external() -> &'static Location<'static> {
    companion::outside()
}

#[track_caller]
#[inline(never)]
pub fn external_panic() {
    companion::raise()
}

#[track_caller]
#[inline(never)]
pub fn local_panic() {
    panic!("tracked local panic");
}

#[track_caller]
#[inline(never)]
pub fn on_assert(n: u64) -> u64 {
    1 / n
}

pub const ASSERT_LINE: u32 = line!() + 3;
#[inline(never)]
pub fn plain_div(n: u64) -> u64 {
    1 / n
}

pub trait Plain {
    fn locate(&self) -> &'static Location<'static>;
}
pub const PLAIN_IMPL_LINE: u32 = line!() + 4;
impl Plain for Marker {
    #[track_caller]
    #[inline(never)]
    fn locate(&self) -> &'static Location<'static> {
        leaf()
    }
}
#[inline(never)]
pub fn plain_dynamic(obj: &dyn Plain) -> &'static Location<'static> {
    obj.locate()
}
