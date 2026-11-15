#![no_std]
use wide_projection_types::*;
#[unsafe(no_mangle)]
pub fn slice_set(p: &mut Holder<[u64]>, v: Owner<[u64]>) -> () {
    p.item = v;
}
#[unsafe(no_mangle)]
pub fn slice_get(p: &Holder<[u64]>) -> Owner<[u64]> {
    p.item
}
#[unsafe(no_mangle)]
pub fn slice_take(p: Holder<[u64]>) -> Owner<[u64]> {
    p.item
}
#[unsafe(no_mangle)]
pub fn slice_byval(mut p: Holder<[u64]>, v: Owner<[u64]>) -> Holder<[u64]> {
    p.item = v;
    p
}
#[unsafe(no_mangle)]
pub fn slice_nested_set(p: &mut Outer<[u64]>, v: Owner<[u64]>) -> () {
    p.inner.item = v;
}
#[unsafe(no_mangle)]
pub fn slice_nested_get(p: &Outer<[u64]>) -> Owner<[u64]> {
    p.inner.item
}
#[unsafe(no_mangle)]
pub fn slice_enum_set(p: &mut Choice<[u64]>, v: Owner<[u64]>) -> () {
    if let Choice::Some { item, .. } = p {
        *item = v;
    }
}
#[unsafe(no_mangle)]
pub fn slice_enum_get(p: &Choice<[u64]>) -> Owner<[u64]> {
    if let Choice::Some { item, .. } = p {
        *item
    } else {
        unsafe { core::hint::unreachable_unchecked() }
    }
}
#[unsafe(no_mangle)]
pub fn slice_copy_pair(p: *mut Owner<[u64]>, q: *const Owner<[u64]>) -> () {
    unsafe {
        *p = *q;
    }
}
#[unsafe(no_mangle)]
pub fn slice_replace(p: &mut Holder<[u64]>, v: Owner<[u64]>) -> Owner<[u64]> {
    core::mem::replace(&mut p.item, v)
}
#[unsafe(no_mangle)]
pub fn text_set(p: &mut Holder<str>, v: Owner<str>) -> () {
    p.item = v;
}
#[unsafe(no_mangle)]
pub fn text_get(p: &Holder<str>) -> Owner<str> {
    p.item
}
#[unsafe(no_mangle)]
pub fn text_take(p: Holder<str>) -> Owner<str> {
    p.item
}
#[unsafe(no_mangle)]
pub fn text_byval(mut p: Holder<str>, v: Owner<str>) -> Holder<str> {
    p.item = v;
    p
}
#[unsafe(no_mangle)]
pub fn text_nested_set(p: &mut Outer<str>, v: Owner<str>) -> () {
    p.inner.item = v;
}
#[unsafe(no_mangle)]
pub fn text_nested_get(p: &Outer<str>) -> Owner<str> {
    p.inner.item
}
#[unsafe(no_mangle)]
pub fn text_enum_set(p: &mut Choice<str>, v: Owner<str>) -> () {
    if let Choice::Some { item, .. } = p {
        *item = v;
    }
}
#[unsafe(no_mangle)]
pub fn text_enum_get(p: &Choice<str>) -> Owner<str> {
    if let Choice::Some { item, .. } = p {
        *item
    } else {
        unsafe { core::hint::unreachable_unchecked() }
    }
}
#[unsafe(no_mangle)]
pub fn text_copy_pair(p: *mut Owner<str>, q: *const Owner<str>) -> () {
    unsafe {
        *p = *q;
    }
}
#[unsafe(no_mangle)]
pub fn text_replace(p: &mut Holder<str>, v: Owner<str>) -> Owner<str> {
    core::mem::replace(&mut p.item, v)
}
#[unsafe(no_mangle)]
pub fn object_set(p: &mut Holder<dyn Eval>, v: Owner<dyn Eval>) -> () {
    p.item = v;
}
#[unsafe(no_mangle)]
pub fn object_get(p: &Holder<dyn Eval>) -> Owner<dyn Eval> {
    p.item
}
#[unsafe(no_mangle)]
pub fn object_take(p: Holder<dyn Eval>) -> Owner<dyn Eval> {
    p.item
}
#[unsafe(no_mangle)]
pub fn object_byval(mut p: Holder<dyn Eval>, v: Owner<dyn Eval>) -> Holder<dyn Eval> {
    p.item = v;
    p
}
#[unsafe(no_mangle)]
pub fn object_nested_set(p: &mut Outer<dyn Eval>, v: Owner<dyn Eval>) -> () {
    p.inner.item = v;
}
#[unsafe(no_mangle)]
pub fn object_nested_get(p: &Outer<dyn Eval>) -> Owner<dyn Eval> {
    p.inner.item
}
#[unsafe(no_mangle)]
pub fn object_enum_set(p: &mut Choice<dyn Eval>, v: Owner<dyn Eval>) -> () {
    if let Choice::Some { item, .. } = p {
        *item = v;
    }
}
#[unsafe(no_mangle)]
pub fn object_enum_get(p: &Choice<dyn Eval>) -> Owner<dyn Eval> {
    if let Choice::Some { item, .. } = p {
        *item
    } else {
        unsafe { core::hint::unreachable_unchecked() }
    }
}
#[unsafe(no_mangle)]
pub fn object_copy_pair(p: *mut Owner<dyn Eval>, q: *const Owner<dyn Eval>) -> () {
    unsafe {
        *p = *q;
    }
}
#[unsafe(no_mangle)]
pub fn object_replace(p: &mut Holder<dyn Eval>, v: Owner<dyn Eval>) -> Owner<dyn Eval> {
    core::mem::replace(&mut p.item, v)
}
