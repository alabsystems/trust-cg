extern crate wide_owner_types;
use std::sync::atomic::{AtomicUsize, Ordering};
use wide_owner_types::*;
static CHECKS: AtomicUsize = AtomicUsize::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static LENGTH: AtomicUsize = AtomicUsize::new(0);
fn check(ok: bool) {
    assert!(ok);
    CHECKS.fetch_add(1, Ordering::Relaxed);
}
fn byte(i: usize, n: usize) -> u8 {
    (33 + (i * 17 + n * 3) % 90) as u8
}
fn word(i: usize, n: usize) -> u64 {
    (i as u64).wrapping_mul(0xd6e8_feb8_6659_fd93) ^ n as u64
}
trait Image {
    type Guard;
    fn guard(&self) -> Self::Guard;
    fn released(guard: &Self::Guard) -> bool;
    fn ptr(&self) -> usize;
    fn inspect(&self, n: usize);
}
macro_rules! payload {
    ($value:expr, $n:expr, bytes) => {{
        check($value.len() == $n);
        check($value.iter().enumerate().all(|(i, x)| *x == byte(i, $n)));
    }};
    ($value:expr, $n:expr, words) => {{
        check($value.len() == $n);
        check($value.iter().enumerate().all(|(i, x)| *x == word(i, $n)));
    }};
    ($value:expr, $n:expr, text) => {
        payload!($value.as_bytes(), $n, bytes);
    };
    ($value:expr, $n:expr, ctext) => {
        payload!($value.to_bytes(), $n, bytes);
    };
}
macro_rules! owned {
    ($ty:ty, $view:ident) => {
        impl Image for $ty {
            type Guard = ();
            fn guard(&self) {}
            fn released(_: &()) -> bool {
                true
            }
            fn ptr(&self) -> usize {
                self.as_ptr() as *const () as usize
            }
            fn inspect(&self, n: usize) {
                payload!(self, n, $view);
                check(true);
            }
        }
    };
}
owned!(Box<[u8]>, bytes);
owned!(Box<[u64]>, words);
owned!(Box<str>, text);
owned!(Box<CStr>, ctext);
impl Image for CString {
    type Guard = ();
    fn guard(&self) {}
    fn released(_: &()) -> bool {
        true
    }
    fn ptr(&self) -> usize {
        self.as_ptr() as usize
    }
    fn inspect(&self, n: usize) {
        payload!(self.as_c_str(), n, ctext);
        check(true);
    }
}
macro_rules! shared {
    ($owner:ident, $weak:ty, $inner:ty, $view:ident) => {
        impl Image for $owner<$inner> {
            type Guard = $weak;
            fn guard(&self) -> Self::Guard {
                $owner::downgrade(self)
            }
            fn released(w: &Self::Guard) -> bool {
                w.strong_count() == 0 && w.upgrade().is_none()
            }
            fn ptr(&self) -> usize {
                self.as_ptr() as *const () as usize
            }
            fn inspect(&self, n: usize) {
                payload!(self, n, $view);
                check($owner::strong_count(self) == 1 && $owner::weak_count(self) == 1);
            }
        }
    };
}
shared!(Rc, std::rc::Weak<[u8]>, [u8], bytes);
shared!(Rc, std::rc::Weak<[u64]>, [u64], words);
shared!(Rc, std::rc::Weak<str>, str, text);
shared!(Arc, std::sync::Weak<[u8]>, [u8], bytes);
shared!(Arc, std::sync::Weak<[u64]>, [u64], words);
shared!(Arc, std::sync::Weak<str>, str, text);
fn callback<T: Image>(v: T) -> T {
    v.inspect(LENGTH.load(Ordering::Relaxed));
    CALLS.fetch_add(1, Ordering::Relaxed);
    v
}
fn wrapper_callback<T: Image>(outer: &mut Envelope<T>) {
    check(outer.head == 11);
    check(outer.tail == 29);
    outer.head = 0xdead_beef;
    outer.tail = 0x1234;
    outer.owner.value.inspect(LENGTH.load(Ordering::Relaxed));
    CALLS.fetch_add(1, Ordering::Relaxed);
}
fn stack_callback<T: Image>(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    value: T,
    suffix: u64,
    result: &mut u64,
) -> T {
    let n = LENGTH.load(Ordering::Relaxed);
    check(
        [a, b, c, d, e, f, g, suffix]
            == [
                n as u64,
                u64::MAX,
                0xdead_beef,
                23,
                0x8765_4321_fedc_ba98,
                0,
                19,
                0x8123,
            ],
    );
    *result = a.rotate_left(1)
        ^ b.rotate_left(7)
        ^ c.rotate_left(13)
        ^ d.rotate_left(19)
        ^ e.rotate_left(23)
        ^ f.rotate_left(29)
        ^ g.rotate_left(31)
        ^ suffix.rotate_left(41);
    callback(value)
}
unsafe extern "Rust" {
    fn borrowed_stack(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        value: &[u8],
        suffix: u64,
    ) -> u64;
    fn borrowed_call_stack(
        value: &[u8],
        callback: fn(u64, u64, u64, u64, u64, u64, u64, &[u8], u64) -> u64,
    ) -> u64;
}
fn borrowed_callback(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    value: &[u8],
    suffix: u64,
) -> u64 {
    check([a, b, c, d, e, f, g, suffix] == [1, 2, 4, 8, 16, 32, 64, 128]);
    check(
        value
            .iter()
            .enumerate()
            .all(|(i, x)| *x == byte(i, value.len())),
    );
    a ^ b ^ c ^ d ^ e ^ f ^ g ^ suffix ^ value.len() as u64
}
type Stack<T> = unsafe fn(u64, u64, u64, u64, u64, u64, u64, T, u64, &mut u64, fn(T) -> T) -> T;
fn exercise<T: Image>(
    n: usize,
    make: impl Fn(usize) -> T,
    identity: unsafe fn(T) -> T,
    relay: unsafe fn(T, fn(T) -> T) -> T,
    cycle: unsafe fn(T, fn(T) -> T, usize) -> T,
    stack: Stack<T>,
    call_stack: unsafe fn(
        T,
        u64,
        &mut u64,
        fn(u64, u64, u64, u64, u64, u64, u64, T, u64, &mut u64) -> T,
    ) -> T,
    wrap: unsafe fn(T, fn(&mut Envelope<T>)) -> T,
) {
    LENGTH.store(n, Ordering::Relaxed);
    for mode in 0..6 {
        let value = make(n);
        let guard = value.guard();
        let before = value.ptr();
        let x = [
            n as u64,
            0xffff_ffff_ffff_ffff,
            0xdead_beef,
            23,
            0x8765_4321_fedc_ba98,
            0,
            19,
            0x8123,
        ];
        let expected = x[0].rotate_left(1)
            ^ x[1].rotate_left(7)
            ^ x[2].rotate_left(13)
            ^ x[3].rotate_left(19)
            ^ x[4].rotate_left(23)
            ^ x[5].rotate_left(29)
            ^ x[6].rotate_left(31)
            ^ x[7].rotate_left(41);
        let mut result = 0;
        CALLS.store(0, Ordering::Relaxed);
        let (returned, calls) = unsafe {
            match mode {
                0 => (identity(value), 0),
                1 => (relay(value, callback::<T>), 1),
                2 => (cycle(value, callback::<T>, n % 7), n % 7),
                3 => (
                    stack(
                        x[0],
                        x[1],
                        x[2],
                        x[3],
                        x[4],
                        x[5],
                        x[6],
                        value,
                        x[7],
                        &mut result,
                        callback::<T>,
                    ),
                    1,
                ),
                4 => (
                    call_stack(value, n as u64, &mut result, stack_callback::<T>),
                    1,
                ),
                _ => (wrap(value, wrapper_callback::<T>), 1),
            }
        };
        returned.inspect(n);
        check(returned.ptr() == before);
        check(CALLS.load(Ordering::Relaxed) == calls);
        check(result == if (3..=4).contains(&mode) { expected } else { 0 });
        drop(returned);
        check(T::released(&guard));
    }
}
macro_rules! declarations {
    ($identity:ident, $relay:ident, $cycle:ident, $stack:ident, $call_stack:ident, $wrap:ident, $ty:ty) => {
        unsafe extern "Rust" {
            fn $wrap(v: $ty, cb: fn(&mut Envelope<$ty>)) -> $ty;
            fn $call_stack(
                v: $ty,
                n: u64,
                r: &mut u64,
                cb: fn(u64, u64, u64, u64, u64, u64, u64, $ty, u64, &mut u64) -> $ty,
            ) -> $ty;
            fn $identity(v: $ty) -> $ty;
            fn $relay(v: $ty, f: fn($ty) -> $ty) -> $ty;
            fn $cycle(v: $ty, f: fn($ty) -> $ty, n: usize) -> $ty;
            fn $stack(
                a: u64,
                b: u64,
                c: u64,
                d: u64,
                e: u64,
                f: u64,
                g: u64,
                v: $ty,
                h: u64,
                r: &mut u64,
                cb: fn($ty) -> $ty,
            ) -> $ty;
        }
    };
}
declarations!(
    box_bytes,
    box_bytes_relay,
    box_bytes_cycle,
    box_bytes_stack,
    box_bytes_call_stack,
    box_bytes_wrap,
    Box<[u8]>
);
declarations!(
    box_words,
    box_words_relay,
    box_words_cycle,
    box_words_stack,
    box_words_call_stack,
    box_words_wrap,
    Box<[u64]>
);
declarations!(
    box_str,
    box_str_relay,
    box_str_cycle,
    box_str_stack,
    box_str_call_stack,
    box_str_wrap,
    Box<str>
);
declarations!(
    box_cstr,
    box_cstr_relay,
    box_cstr_cycle,
    box_cstr_stack,
    box_cstr_call_stack,
    box_cstr_wrap,
    Box<CStr>
);
declarations!(
    rc_bytes,
    rc_bytes_relay,
    rc_bytes_cycle,
    rc_bytes_stack,
    rc_bytes_call_stack,
    rc_bytes_wrap,
    Rc<[u8]>
);
declarations!(
    rc_words,
    rc_words_relay,
    rc_words_cycle,
    rc_words_stack,
    rc_words_call_stack,
    rc_words_wrap,
    Rc<[u64]>
);
declarations!(
    rc_str,
    rc_str_relay,
    rc_str_cycle,
    rc_str_stack,
    rc_str_call_stack,
    rc_str_wrap,
    Rc<str>
);
declarations!(
    arc_bytes,
    arc_bytes_relay,
    arc_bytes_cycle,
    arc_bytes_stack,
    arc_bytes_call_stack,
    arc_bytes_wrap,
    Arc<[u8]>
);
declarations!(
    arc_words,
    arc_words_relay,
    arc_words_cycle,
    arc_words_stack,
    arc_words_call_stack,
    arc_words_wrap,
    Arc<[u64]>
);
declarations!(
    arc_str,
    arc_str_relay,
    arc_str_cycle,
    arc_str_stack,
    arc_str_call_stack,
    arc_str_wrap,
    Arc<str>
);
declarations!(
    cstring,
    cstring_relay,
    cstring_cycle,
    cstring_stack,
    cstring_call_stack,
    cstring_wrap,
    CString
);
fn bytes(n: usize) -> Vec<u8> {
    (0..n).map(|i| byte(i, n)).collect()
}
fn words(n: usize) -> Vec<u64> {
    (0..n).map(|i| word(i, n)).collect()
}
fn text(n: usize) -> String {
    String::from_utf8(bytes(n)).unwrap()
}
fn main() {
    for n in 0..258 {
        let data = bytes(n);
        check(unsafe { borrowed_stack(1, 2, 4, 8, 16, 32, 64, &data, 128) } == 255 ^ n as u64);
        check(unsafe { borrowed_call_stack(&data, borrowed_callback) } == 255 ^ n as u64);

        exercise(
            n,
            |n| bytes(n).into_boxed_slice(),
            box_bytes,
            box_bytes_relay,
            box_bytes_cycle,
            box_bytes_stack,
            box_bytes_call_stack,
            box_bytes_wrap,
        );
        exercise(
            n,
            |n| words(n).into_boxed_slice(),
            box_words,
            box_words_relay,
            box_words_cycle,
            box_words_stack,
            box_words_call_stack,
            box_words_wrap,
        );
        exercise(
            n,
            |n| text(n).into_boxed_str(),
            box_str,
            box_str_relay,
            box_str_cycle,
            box_str_stack,
            box_str_call_stack,
            box_str_wrap,
        );
        exercise(
            n,
            |n| CString::new(bytes(n)).unwrap().into_boxed_c_str(),
            box_cstr,
            box_cstr_relay,
            box_cstr_cycle,
            box_cstr_stack,
            box_cstr_call_stack,
            box_cstr_wrap,
        );
        exercise(
            n,
            |n| Rc::from(bytes(n)),
            rc_bytes,
            rc_bytes_relay,
            rc_bytes_cycle,
            rc_bytes_stack,
            rc_bytes_call_stack,
            rc_bytes_wrap,
        );
        exercise(
            n,
            |n| Rc::from(words(n)),
            rc_words,
            rc_words_relay,
            rc_words_cycle,
            rc_words_stack,
            rc_words_call_stack,
            rc_words_wrap,
        );
        exercise(
            n,
            |n| Rc::from(text(n)),
            rc_str,
            rc_str_relay,
            rc_str_cycle,
            rc_str_stack,
            rc_str_call_stack,
            rc_str_wrap,
        );
        exercise(
            n,
            |n| Arc::from(bytes(n)),
            arc_bytes,
            arc_bytes_relay,
            arc_bytes_cycle,
            arc_bytes_stack,
            arc_bytes_call_stack,
            arc_bytes_wrap,
        );
        exercise(
            n,
            |n| Arc::from(words(n)),
            arc_words,
            arc_words_relay,
            arc_words_cycle,
            arc_words_stack,
            arc_words_call_stack,
            arc_words_wrap,
        );
        exercise(
            n,
            |n| Arc::from(text(n)),
            arc_str,
            arc_str_relay,
            arc_str_cycle,
            arc_str_stack,
            arc_str_call_stack,
            arc_str_wrap,
        );
        exercise(
            n,
            |n| CString::new(bytes(n)).unwrap(),
            cstring,
            cstring_relay,
            cstring_cycle,
            cstring_stack,
            cstring_call_stack,
            cstring_wrap,
        );
    }
    println!("PASS wide_owner checks={}", CHECKS.load(Ordering::Relaxed));
}
