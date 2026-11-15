//! Other fat-leaf kinds stored whole through a field projection.
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;
pub struct Sl { pub a: u8, pub s: &'static [u16], pub b: u32 }
pub struct Nn { pub a: u16, pub p: NonNull<[u8]>, pub b: u8 }
pub struct Dy { pub a: u8, pub d: Box<dyn Fn(u64) -> u64>, pub b: u16 }
pub struct Rcs { pub a: u8, pub r: Rc<[u8]>, pub s: Arc<str>, pub b: u8 }
pub struct Opt { pub a: u8, pub o: Option<Box<[u8]>>, pub b: u8 }
pub struct Pair { pub a: u8, pub w: (Box<[u8]>, u32), pub b: u8 }
#[inline(never)]
pub fn set_slice(t: &mut Sl, s: &'static [u16]) { t.s = s; }
#[inline(never)]
pub fn set_nonnull(t: &mut Nn, p: NonNull<[u8]>) { t.p = p; }
#[inline(never)]
pub fn set_dyn(t: &mut Dy, d: Box<dyn Fn(u64) -> u64>) { t.d = d; }
#[inline(never)]
pub fn set_rc(t: &mut Rcs, r: Rc<[u8]>, s: Arc<str>) { t.r = r; t.s = s; }
#[inline(never)]
pub fn set_opt(t: &mut Opt, o: Option<Box<[u8]>>) { t.o = o; }
#[inline(never)]
pub fn set_pair(t: &mut Pair, w: (Box<[u8]>, u32)) { t.w = w; }
pub struct Inner { pub tag: u8, pub b: Box<[u8]>, pub n: u32 }
pub struct OuterK { pub a: u64, pub w: Inner, pub z: u16 }
/// A whole multi-field struct holding a box, stored through a field.
#[inline(never)]
pub fn set_w(o: &mut OuterK, w: Inner) { o.w = w; }
