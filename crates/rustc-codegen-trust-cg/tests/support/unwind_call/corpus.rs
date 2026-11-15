#![no_std]
unsafe extern "Rust" {
    fn unwind_step(v: u64) -> u64;
    fn unwind_mut_step(cell: &mut u64, v: u64) -> u64;
}
unsafe extern "C" {
    fn unwind_event(kind: u64, value: u64);
}
struct Guard(*const u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { unwind_event(5, *self.0) }
    }
}
struct Marker;
impl Drop for Marker {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { unwind_event(5, 0) }
    }
}
#[inline(never)]
fn capture<F: FnOnce() -> u64>(f: F) -> u64 {
    f()
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_cell(v: u64) -> u64 {
    let mut out = v ^ 0x55;
    let seen = capture(|| out);
    unsafe {
        unwind_event(3, seen);
    }
    let _guard = Guard(&raw const out);
    out = unsafe { unwind_step(v) };
    unsafe {
        unwind_event(2, out);
    }
    out
}
#[repr(C)]
struct Fields {
    a: u64,
    b: u64,
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_projected(v: u64) -> u64 {
    let mut fields = Fields { a: v, b: v ^ 0x55 };
    let _guard = Guard(&raw const fields.b);
    fields.b = unsafe { unwind_step(v) };
    unsafe {
        unwind_event(2, fields.b);
    }
    fields.b ^ fields.a
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_reload(v: u64) -> u64 {
    let _guard = Marker;
    let mut cell = v ^ 0x55;
    let result = unsafe { unwind_mut_step(&mut cell, v) };
    unsafe {
        unwind_event(2, cell);
    }
    result ^ cell
}
#[inline(never)]
fn closure_cell<F: FnMut(u64) -> u64>(mut f: F, v: u64) -> u64 {
    let mut out = v ^ 0x55;
    let seen = capture(|| out);
    unsafe {
        unwind_event(3, seen);
    }
    let _guard = Guard(&raw const out);
    out = f(v);
    unsafe {
        unwind_event(2, out);
    }
    out
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_closure_cell(v: u64) -> u64 {
    closure_cell(|x| unsafe { unwind_step(x) }, v)
}
#[inline(never)]
fn closure_pair<F: FnMut(u64) -> (u64, u64)>(mut f: F, v: u64) -> u64 {
    let _guard = Marker;
    let pair = f(v);
    let out = pair.0 ^ pair.1;
    unsafe {
        unwind_event(2, out);
    }
    out
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_closure_pair(v: u64) -> u64 {
    closure_pair(|x| (unsafe { unwind_step(x) }, x ^ 0x77), v)
}
#[repr(C)]
struct Words {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
}
#[inline(never)]
fn closure_words<F: FnMut(u64) -> Words>(mut f: F, v: u64) -> u64 {
    let _guard = Marker;
    let words = f(v);
    let out = words.a ^ words.b ^ words.c ^ words.d;
    unsafe {
        unwind_event(2, out);
    }
    out
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_closure_words(v: u64) -> u64 {
    closure_words(
        |x| Words {
            a: unsafe { unwind_step(x) },
            b: x ^ 0x11,
            c: !x,
            d: x.wrapping_mul(31),
        },
        v,
    )
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_loop(v: u64) -> u64 {
    let mut out = v ^ 0x55;
    let _guard = Guard(&raw const out);
    let mut i = 0u64;
    while i < 4 {
        if i & 1 == 0 {
            out = unsafe { unwind_step(out) };
        } else {
            out = unsafe { unwind_step(out ^ i) };
        }
        i += 1;
    }
    unsafe {
        unwind_event(2, out);
    }
    out
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_scalarized_projected(v: u64) -> u64 {
    let _guard = Marker;
    let mut fields = Fields { a: v, b: v ^ 0x55 };
    fields.b = unsafe { unwind_step(v) };
    unsafe {
        unwind_event(2, fields.b);
    }
    fields.b ^ fields.a
}
#[inline(never)]
fn closure_projected<F: FnMut(u64) -> u64>(mut f: F, v: u64) -> u64 {
    let _guard = Marker;
    let mut fields = Fields { a: v, b: v ^ 0x55 };
    fields.b = f(v);
    unsafe {
        unwind_event(2, fields.b);
    }
    fields.b ^ fields.a
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_closure_projected(v: u64) -> u64 {
    closure_projected(|x| unsafe { unwind_step(x) }, v)
}

unsafe extern "Rust" {
    fn unwind_lt(a: u64, b: u64) -> bool;
}
#[inline(never)]
fn select_min<T, F: FnMut(&T, &T) -> bool>(a: T, b: T, mut f: F) -> T {
    if f(&a, &b) { a } else { b }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_select_min(v: u64) -> u64 {
    let _guard = Marker;
    let out = select_min(v, v.rotate_left(31) ^ 0xabcdef, |a, b| unsafe {
        unwind_lt(*a, *b)
    });
    unsafe {
        unwind_event(2, out);
    }
    out
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_alias_destination(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    cell = unsafe { unwind_mut_step(&mut cell, v) };
    unsafe {
        unwind_event(2, cell);
    }
    cell
}
