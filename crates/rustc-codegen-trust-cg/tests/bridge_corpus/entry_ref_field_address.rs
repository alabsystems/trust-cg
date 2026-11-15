// A reference to a FIELD of the pointee of a thin reference ENTRY ARGUMENT,
// stored into a scalar cell: `_n = &(*arg).f` where `&_n` is unsized to a
// `&dyn` (derived `Debug`'s `&&self.last_field`). The stored value must be the
// field's real address, `arg + rustc layout offset`.
//
// Before the fix the x86-64 macOS bridge refused every function below except
// `peek_q` and `pass_inner` with `Place deref memory store from Rvalue::Ref
// (projected source's base is not a reference to a memory-eligible aggregate)`
// (a pointer, primitive-wrapper or tuple field), or `Ty::Adt multi-field struct
// Inner` (a nested-struct field): `<core::ffi::va_list::VaListInner as
// Debug>::fmt` is `VaLike`'s shape exactly. Each check reads the field back
// through the stored address, so a wrong offset reads a sibling and changes the
// exit code; `write_reg` writes through a `&mut` field reference and the caller
// checks the write landed in its own struct and nowhere else.
#![feature(formatting_options)]
use core::ffi::c_void;
use core::fmt;
use std::hint::black_box;

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct VaLike {
    pub gp_offset: i32,
    pub fp_offset: i32,
    pub overflow_arg_area: *const c_void,
    pub reg_save_area: *const c_void,
}

#[derive(Debug, Clone, Copy)]
pub struct Reordered {
    pub a: u8,
    pub p: *const u8,
    pub b: u16,
    pub q: *const u32,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Inner {
    pub x: u64,
    pub p: *const u8,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Outer {
    pub tag: u64,
    pub inner: Inner,
}

#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct W(pub *const u8);

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Wrapped {
    pub n: u32,
    pub w: W,
}

impl fmt::Debug for Wrapped {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let p = &self.w.0;
        f.debug_struct("Wrapped").field("n", &self.n).field("w0", &p).finish()
    }
}

pub trait Peek {
    fn peek(&self) -> u64;
}
impl Peek for &*const c_void {
    fn peek(&self) -> u64 {
        **self as u64
    }
}
impl Peek for &mut *const c_void {
    fn peek(&self) -> u64 {
        **self as u64
    }
}
impl Peek for &*const u8 {
    fn peek(&self) -> u64 {
        **self as u64
    }
}
impl Peek for &*const u32 {
    fn peek(&self) -> u64 {
        **self as u64
    }
}
impl Peek for &Inner {
    fn peek(&self) -> u64 {
        self.x + self.p as u64
    }
}

#[inline(never)]
pub fn peek_reg(v: &VaLike) -> u64 {
    let r = &v.reg_save_area;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
pub fn peek_overflow(v: &VaLike) -> u64 {
    let r = &v.overflow_arg_area;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
pub fn write_reg(v: &mut VaLike, np: *const c_void) -> u64 {
    let r = &mut v.reg_save_area;
    let d: &dyn Peek = &r;
    let old = d.peek();
    *r = np;
    old + v.reg_save_area as u64
}

#[inline(never)]
pub fn peek_q(v: &Reordered) -> u64 {
    let r = &v.q;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
pub fn peek_w(v: &Wrapped) -> u64 {
    let r = &v.w.0;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
pub fn peek_inner(v: &Outer) -> u64 {
    let r = &v.inner;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
pub fn peek_tuple(t: &(u32, *const u8)) -> u64 {
    let r = &t.1;
    let d: &dyn Peek = &r;
    d.peek()
}

#[inline(never)]
fn take(r: &&Inner) -> u64 {
    r.x + r.p as u64
}

#[inline(never)]
pub fn pass_inner(v: &Outer) -> u64 {
    let r = &v.inner;
    take(&r)
}

struct Cmp<'a> {
    want: &'a [u8],
    pos: usize,
    ok: bool,
}

impl fmt::Write for Cmp<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &b in s.as_bytes() {
            if self.pos >= self.want.len() || self.want[self.pos] != b {
                self.ok = false;
            }
            self.pos += 1;
        }
        Ok(())
    }
}

#[inline(never)]
fn debug_is<T: fmt::Debug>(v: &T, want: &str) -> bool {
    let mut c = Cmp {
        want: want.as_bytes(),
        pos: 0,
        ok: true,
    };
    let mut f = fmt::Formatter::new(&mut c, fmt::FormattingOptions::new());
    let r = fmt::Debug::fmt(v, &mut f).is_ok();
    r && c.ok && c.pos == c.want.len()
}

fn main() {
    let mut v = black_box(VaLike {
        gp_offset: 1,
        fp_offset: 2,
        overflow_arg_area: 0x1000 as *const c_void,
        reg_save_area: 0x2468 as *const c_void,
    });
    let outer = black_box(Outer {
        tag: 9,
        inner: Inner {
            x: 5,
            p: 0x3000 as *const u8,
        },
    });
    let wrapped = black_box(Wrapped {
        n: 3,
        w: W(0x4400 as *const u8),
    });
    let reordered = black_box(Reordered {
        a: 1,
        p: 0x10 as *const u8,
        b: 2,
        q: 0x5550 as *const u32,
    });
    // Exit 42 when every field read back through its stored address is that
    // field's; otherwise exit 100 + the index of the first failing check.
    let checks = [
        peek_reg(&v) == 0x2468,
        peek_overflow(&v) == 0x1000,
        debug_is(
            &v,
            black_box(
                "VaLike { gp_offset: 1, fp_offset: 2, overflow_arg_area: 0x1000, \
                 reg_save_area: 0x2468 }",
            ),
        ),
        {
            let s = write_reg(&mut v, black_box(0x1357 as *const c_void));
            s == 0x2468 + 0x1357
                && v.reg_save_area as u64 == 0x1357
                && v.overflow_arg_area as u64 == 0x1000
                && v.gp_offset == 1
                && v.fp_offset == 2
        },
        peek_w(&wrapped) == 0x4400,
        debug_is(&wrapped, black_box("Wrapped { n: 3, w0: 0x4400 }")),
        peek_inner(&outer) == 5 + 0x3000,
        debug_is(
            &outer,
            black_box("Outer { tag: 9, inner: Inner { x: 5, p: 0x3000 } }"),
        ),
        pass_inner(&outer) == 5 + 0x3000,
        peek_tuple(&black_box((7u32, 0x6600 as *const u8))) == 0x6600,
        peek_q(&reordered) == 0x5550,
        debug_is(
            &reordered,
            black_box("Reordered { a: 1, p: 0x10, b: 2, q: 0x5550 }"),
        ),
    ];
    let mut i = 0;
    while i < checks.len() {
        if !checks[i] {
            std::process::exit(100 + i as i32);
        }
        i += 1;
    }
    std::process::exit(42);
}
