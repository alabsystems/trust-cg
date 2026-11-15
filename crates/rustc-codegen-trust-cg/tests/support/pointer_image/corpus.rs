#![no_std]
extern crate alloc;
extern crate pointer_image_types;
use core::ptr::NonNull;
use pointer_image_types::*;
macro_rules! cases {
    ($ty:ty, $thin:ident, $nn:ident, $raw:ident, $field_raw:ident, $field_nn:ident, $borrow_nn:ident, $wide:ident) => {
        #[unsafe(no_mangle)]
        pub fn $thin(p: *const $ty) -> *const u8 {
            p as *const u8
        }
        #[unsafe(no_mangle)]
        pub unsafe fn $nn(p: *mut $ty) -> NonNull<$ty> {
            unsafe { NonNull::new_unchecked(p) }
        }
        #[unsafe(no_mangle)]
        pub fn $raw(p: NonNull<$ty>) -> *mut $ty {
            p.as_ptr()
        }
        #[unsafe(no_mangle)]
        pub fn $field_raw(v: Envelope<NonNull<$ty>>) -> *mut $ty {
            unsafe { core::mem::transmute(v.item.value) }
        }
        #[unsafe(no_mangle)]
        pub unsafe fn $field_nn(v: Envelope<*mut $ty>) -> NonNull<$ty> {
            unsafe { core::mem::transmute(v.item.value) }
        }
        #[unsafe(no_mangle)]
        pub fn $borrow_nn(v: &Carrier<NonNull<$ty>>) -> *mut $ty {
            v.value.as_ptr()
        }
        #[unsafe(no_mangle)]
        pub fn $wide(p: *mut $ty) -> *mut [u64] {
            p as *mut [u64]
        }
    };
}
cases!(
    [u8],
    bytes_thin,
    bytes_nn,
    bytes_raw,
    bytes_field_raw,
    bytes_field_nn,
    bytes_borrow_nn,
    bytes_wide
);
cases!(
    [u64],
    words_thin,
    words_nn,
    words_raw,
    words_field_raw,
    words_field_nn,
    words_borrow_nn,
    words_wide
);
cases!(
    str,
    text_thin,
    text_nn,
    text_raw,
    text_field_raw,
    text_field_nn,
    text_borrow_nn,
    text_wide
);
cases!(
    CStr,
    ctext_thin,
    ctext_nn,
    ctext_raw,
    ctext_field_raw,
    ctext_field_nn,
    ctext_borrow_nn,
    ctext_wide
);
cases!(
    Header<[u8]>,
    header_bytes_thin,
    header_bytes_nn,
    header_bytes_raw,
    header_bytes_field_raw,
    header_bytes_field_nn,
    header_bytes_borrow_nn,
    header_bytes_wide
);
cases!(
    Header<[u64]>,
    header_words_thin,
    header_words_nn,
    header_words_raw,
    header_words_field_raw,
    header_words_field_nn,
    header_words_borrow_nn,
    header_words_wide
);
cases!(
    Header<str>,
    header_text_thin,
    header_text_nn,
    header_text_raw,
    header_text_field_raw,
    header_text_field_nn,
    header_text_borrow_nn,
    header_text_wide
);
macro_rules! owner {
    ($ty:ty, $borrow:ident, $raw:ident) => {
        #[unsafe(no_mangle)]
        pub fn $borrow(v: &Box<$ty>) -> *const u8 {
            (&**v as *const $ty) as *const u8
        }
        #[unsafe(no_mangle)]
        pub fn $raw(v: Box<$ty>) -> *mut $ty {
            Box::into_raw(v)
        }
    };
}
owner!([u8], bytes_borrow_box, bytes_box_raw);
owner!([u64], words_borrow_box, words_box_raw);
owner!(str, text_borrow_box, text_box_raw);
owner!(CStr, ctext_borrow_box, ctext_box_raw);
#[unsafe(no_mangle)]
pub fn rc_bytes(v: &Rc<[u8]>) -> *const [u8] {
    Rc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn rc_words(v: &Rc<[u64]>) -> *const [u64] {
    Rc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn rc_text(v: &Rc<str>) -> *const str {
    Rc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn arc_bytes(v: &Arc<[u8]>) -> *const [u8] {
    Arc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn arc_words(v: &Arc<[u64]>) -> *const [u64] {
    Arc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn arc_text(v: &Arc<str>) -> *const str {
    Arc::as_ptr(v)
}
#[unsafe(no_mangle)]
pub fn cstring_bytes(v: &alloc::ffi::CString) -> &[u8] {
    v.as_bytes_with_nul()
}
