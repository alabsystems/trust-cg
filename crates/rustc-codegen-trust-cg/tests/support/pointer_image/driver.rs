#![feature(ptr_metadata)]
extern crate pointer_image_types;
use pointer_image_types::*;
use std::ptr::{self, NonNull, Pointee};
use std::sync::atomic::{AtomicUsize, Ordering};
static CHECKS: AtomicUsize = AtomicUsize::new(0);
fn check(v: bool) {
    assert!(v);
    CHECKS.fetch_add(1, Ordering::Relaxed);
}
fn carrier<P>(p: P) -> Carrier<P> {
    Carrier {
        marker: std::marker::PhantomData,
        value: p,
    }
}
fn envelope<P>(p: P) -> Envelope<P> {
    Envelope {
        head: 0x1234_5678_90ab_cdef,
        item: carrier(p),
        tail: 0xfedc_ba09_8765_4321,
    }
}
#[allow(improper_ctypes)]
unsafe extern "Rust" {
    fn rc_bytes(v: &Rc<[u8]>) -> *const [u8];
    fn rc_words(v: &Rc<[u64]>) -> *const [u64];
    fn rc_text(v: &Rc<str>) -> *const str;
    fn arc_bytes(v: &Arc<[u8]>) -> *const [u8];
    fn arc_words(v: &Arc<[u64]>) -> *const [u64];
    fn arc_text(v: &Arc<str>) -> *const str;
    fn cstring_bytes(v: &std::ffi::CString) -> &[u8];
    fn bytes_thin(p: *const [u8]) -> *const u8;
    fn bytes_nn(p: *mut [u8]) -> NonNull<[u8]>;
    fn bytes_raw(p: NonNull<[u8]>) -> *mut [u8];
    fn bytes_field_raw(v: Envelope<NonNull<[u8]>>) -> *mut [u8];
    fn bytes_field_nn(v: Envelope<*mut [u8]>) -> NonNull<[u8]>;
    fn bytes_borrow_nn(v: &Carrier<NonNull<[u8]>>) -> *mut [u8];
    fn bytes_wide(p: *mut [u8]) -> *mut [u64];
    fn words_thin(p: *const [u64]) -> *const u8;
    fn words_nn(p: *mut [u64]) -> NonNull<[u64]>;
    fn words_raw(p: NonNull<[u64]>) -> *mut [u64];
    fn words_field_raw(v: Envelope<NonNull<[u64]>>) -> *mut [u64];
    fn words_field_nn(v: Envelope<*mut [u64]>) -> NonNull<[u64]>;
    fn words_borrow_nn(v: &Carrier<NonNull<[u64]>>) -> *mut [u64];
    fn words_wide(p: *mut [u64]) -> *mut [u64];
    fn text_thin(p: *const str) -> *const u8;
    fn text_nn(p: *mut str) -> NonNull<str>;
    fn text_raw(p: NonNull<str>) -> *mut str;
    fn text_field_raw(v: Envelope<NonNull<str>>) -> *mut str;
    fn text_field_nn(v: Envelope<*mut str>) -> NonNull<str>;
    fn text_borrow_nn(v: &Carrier<NonNull<str>>) -> *mut str;
    fn text_wide(p: *mut str) -> *mut [u64];
    fn ctext_thin(p: *const CStr) -> *const u8;
    fn ctext_nn(p: *mut CStr) -> NonNull<CStr>;
    fn ctext_raw(p: NonNull<CStr>) -> *mut CStr;
    fn ctext_field_raw(v: Envelope<NonNull<CStr>>) -> *mut CStr;
    fn ctext_field_nn(v: Envelope<*mut CStr>) -> NonNull<CStr>;
    fn ctext_borrow_nn(v: &Carrier<NonNull<CStr>>) -> *mut CStr;
    fn ctext_wide(p: *mut CStr) -> *mut [u64];
    fn header_bytes_thin(p: *const Header<[u8]>) -> *const u8;
    fn header_bytes_nn(p: *mut Header<[u8]>) -> NonNull<Header<[u8]>>;
    fn header_bytes_raw(p: NonNull<Header<[u8]>>) -> *mut Header<[u8]>;
    fn header_bytes_field_raw(v: Envelope<NonNull<Header<[u8]>>>) -> *mut Header<[u8]>;
    fn header_bytes_field_nn(v: Envelope<*mut Header<[u8]>>) -> NonNull<Header<[u8]>>;
    fn header_bytes_borrow_nn(v: &Carrier<NonNull<Header<[u8]>>>) -> *mut Header<[u8]>;
    fn header_bytes_wide(p: *mut Header<[u8]>) -> *mut [u64];
    fn header_words_thin(p: *const Header<[u64]>) -> *const u8;
    fn header_words_nn(p: *mut Header<[u64]>) -> NonNull<Header<[u64]>>;
    fn header_words_raw(p: NonNull<Header<[u64]>>) -> *mut Header<[u64]>;
    fn header_words_field_raw(v: Envelope<NonNull<Header<[u64]>>>) -> *mut Header<[u64]>;
    fn header_words_field_nn(v: Envelope<*mut Header<[u64]>>) -> NonNull<Header<[u64]>>;
    fn header_words_borrow_nn(v: &Carrier<NonNull<Header<[u64]>>>) -> *mut Header<[u64]>;
    fn header_words_wide(p: *mut Header<[u64]>) -> *mut [u64];
    fn header_text_thin(p: *const Header<str>) -> *const u8;
    fn header_text_nn(p: *mut Header<str>) -> NonNull<Header<str>>;
    fn header_text_raw(p: NonNull<Header<str>>) -> *mut Header<str>;
    fn header_text_field_raw(v: Envelope<NonNull<Header<str>>>) -> *mut Header<str>;
    fn header_text_field_nn(v: Envelope<*mut Header<str>>) -> NonNull<Header<str>>;
    fn header_text_borrow_nn(v: &Carrier<NonNull<Header<str>>>) -> *mut Header<str>;
    fn header_text_wide(p: *mut Header<str>) -> *mut [u64];
    fn bytes_borrow_box(v: &Box<[u8]>) -> *const u8;
    fn bytes_box_raw(v: Box<[u8]>) -> *mut [u8];
    fn words_borrow_box(v: &Box<[u64]>) -> *const u8;
    fn words_box_raw(v: Box<[u64]>) -> *mut [u64];
    fn text_borrow_box(v: &Box<str>) -> *const u8;
    fn text_box_raw(v: Box<str>) -> *mut str;
    fn ctext_borrow_box(v: &Box<CStr>) -> *const u8;
    fn ctext_box_raw(v: Box<CStr>) -> *mut CStr;
}
fn image<T: ?Sized + Pointee<Metadata = usize>>(a: *mut T, b: *mut T) {
    check(a as *mut () == b as *mut ());
    check(ptr::metadata(a) == ptr::metadata(b));
}
fn run<T: ?Sized + Pointee<Metadata = usize>>(
    thin: unsafe fn(*const T) -> *const u8,
    nn: unsafe fn(*mut T) -> NonNull<T>,
    raw: unsafe fn(NonNull<T>) -> *mut T,
    field_raw: unsafe fn(Envelope<NonNull<T>>) -> *mut T,
    field_nn: unsafe fn(Envelope<*mut T>) -> NonNull<T>,
    borrow: unsafe fn(&Carrier<NonNull<T>>) -> *mut T,
    wide: unsafe fn(*mut T) -> *mut [u64],
) {
    let mut storage = [0u64; 64];
    for len in (0..=257).chain([usize::MAX, usize::MAX - 1, 1usize << 32, 1usize << 63]) {
        for offset in 0..8 {
            let data = unsafe { storage.as_mut_ptr().add(offset) };
            let p = ptr::from_raw_parts_mut::<T>(data.cast::<()>(), len);
            unsafe {
                check(thin(p) == data.cast());
                let n = nn(p);
                image(n.as_ptr(), p);
                image(raw(n), p);
                image(field_raw(envelope(n)), p);
                image(field_nn(envelope(p)).as_ptr(), p);
                image(borrow(&carrier(n)), p);
                let w = wide(p);
                check(w as *mut () == data.cast());
                check(ptr::metadata(w) == len);
                let null = ptr::from_raw_parts::<T>(ptr::null::<()>(), len);
                check(thin(null).is_null());
            }
        }
    }
}
fn owner<T: ?Sized + Pointee<Metadata = usize>>(
    b: Box<T>,
    borrow: unsafe fn(&Box<T>) -> *const u8,
    raw: unsafe fn(Box<T>) -> *mut T,
) -> Box<T> {
    let expected = (&*b as *const T).cast_mut();
    unsafe {
        check(borrow(&b) == expected as *const u8);
        let p = raw(b);
        image(p, expected);
        Box::from_raw(p)
    }
}
fn main() {
    run::<[u8]>(
        bytes_thin,
        bytes_nn,
        bytes_raw,
        bytes_field_raw,
        bytes_field_nn,
        bytes_borrow_nn,
        bytes_wide,
    );
    run::<[u64]>(
        words_thin,
        words_nn,
        words_raw,
        words_field_raw,
        words_field_nn,
        words_borrow_nn,
        words_wide,
    );
    run::<str>(
        text_thin,
        text_nn,
        text_raw,
        text_field_raw,
        text_field_nn,
        text_borrow_nn,
        text_wide,
    );
    run::<CStr>(
        ctext_thin,
        ctext_nn,
        ctext_raw,
        ctext_field_raw,
        ctext_field_nn,
        ctext_borrow_nn,
        ctext_wide,
    );
    run::<Header<[u8]>>(
        header_bytes_thin,
        header_bytes_nn,
        header_bytes_raw,
        header_bytes_field_raw,
        header_bytes_field_nn,
        header_bytes_borrow_nn,
        header_bytes_wide,
    );
    run::<Header<[u64]>>(
        header_words_thin,
        header_words_nn,
        header_words_raw,
        header_words_field_raw,
        header_words_field_nn,
        header_words_borrow_nn,
        header_words_wide,
    );
    run::<Header<str>>(
        header_text_thin,
        header_text_nn,
        header_text_raw,
        header_text_field_raw,
        header_text_field_nn,
        header_text_borrow_nn,
        header_text_wide,
    );
    for n in 0..=257 {
        let bytes: Vec<u8> = (0..n).map(|i| 33 + ((i * 17 + n * 3) % 90) as u8).collect();
        let words: Vec<u64> = (0..n)
            .map(|i| (i as u64).wrapping_mul(0xd6e8_feb8_6659_fd93) ^ n as u64)
            .collect();
        let b = owner(
            bytes.clone().into_boxed_slice(),
            bytes_borrow_box,
            bytes_box_raw,
        );
        check(&*b == &bytes);
        drop(b);
        let w = owner(
            words.clone().into_boxed_slice(),
            words_borrow_box,
            words_box_raw,
        );
        check(&*w == &words);
        drop(w);
        let text = String::from_utf8(bytes.clone()).unwrap();
        let s = owner(text.clone().into_boxed_str(), text_borrow_box, text_box_raw);
        check(&*s == text);
        drop(s);
        {
            let v = Rc::<[u8]>::from(bytes.clone().into_boxed_slice());
            let w = Rc::downgrade(&v);
            let expected = Rc::as_ptr(&v);
            let p = unsafe { rc_bytes(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &bytes[..]);
            check(Rc::strong_count(&v) == 1 && Rc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        {
            let v = Rc::<[u64]>::from(words.clone().into_boxed_slice());
            let w = Rc::downgrade(&v);
            let expected = Rc::as_ptr(&v);
            let p = unsafe { rc_words(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &words[..]);
            check(Rc::strong_count(&v) == 1 && Rc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        {
            let v = Rc::<str>::from(text.clone().into_boxed_str());
            let w = Rc::downgrade(&v);
            let expected = Rc::as_ptr(&v);
            let p = unsafe { rc_text(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &text[..]);
            check(Rc::strong_count(&v) == 1 && Rc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        {
            let v = Arc::<[u8]>::from(bytes.clone().into_boxed_slice());
            let w = Arc::downgrade(&v);
            let expected = Arc::as_ptr(&v);
            let p = unsafe { arc_bytes(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &bytes[..]);
            check(Arc::strong_count(&v) == 1 && Arc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        {
            let v = Arc::<[u64]>::from(words.clone().into_boxed_slice());
            let w = Arc::downgrade(&v);
            let expected = Arc::as_ptr(&v);
            let p = unsafe { arc_words(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &words[..]);
            check(Arc::strong_count(&v) == 1 && Arc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        {
            let v = Arc::<str>::from(text.clone().into_boxed_str());
            let w = Arc::downgrade(&v);
            let expected = Arc::as_ptr(&v);
            let p = unsafe { arc_text(&v) };
            image(p.cast_mut(), expected.cast_mut());
            check(unsafe { &*p } == &text[..]);
            check(Arc::strong_count(&v) == 1 && Arc::weak_count(&v) == 1);
            drop(v);
            check(w.upgrade().is_none());
        }
        let c = std::ffi::CString::new(bytes.clone()).unwrap();
        let view = unsafe { cstring_bytes(&c) };
        check(view.as_ptr() == c.as_ptr().cast());
        check(view == c.as_bytes_with_nul());
        let c = owner(c.into_boxed_c_str(), ctext_borrow_box, ctext_box_raw);
        check(c.to_bytes() == bytes);
        drop(c);
    }
    println!(
        "PASS pointer_image checks={}",
        CHECKS.load(Ordering::Relaxed)
    );
}
