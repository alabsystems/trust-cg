#![feature(ptr_metadata)]
use std::{marker::PhantomData, ptr::NonNull};
use wide_projection_types::*;
unsafe extern "Rust" {
    fn slice_set(p: &mut Holder<[u64]>, v: Owner<[u64]>) -> ();
    fn slice_get(p: &Holder<[u64]>) -> Owner<[u64]>;
    fn slice_take(p: Holder<[u64]>) -> Owner<[u64]>;
    fn slice_byval(p: Holder<[u64]>, v: Owner<[u64]>) -> Holder<[u64]>;
    fn slice_nested_set(p: &mut Outer<[u64]>, v: Owner<[u64]>) -> ();
    fn slice_nested_get(p: &Outer<[u64]>) -> Owner<[u64]>;
    fn slice_enum_set(p: &mut Choice<[u64]>, v: Owner<[u64]>) -> ();
    fn slice_enum_get(p: &Choice<[u64]>) -> Owner<[u64]>;
    fn slice_copy_pair(p: *mut Owner<[u64]>, q: *const Owner<[u64]>) -> ();
    fn slice_replace(p: &mut Holder<[u64]>, v: Owner<[u64]>) -> Owner<[u64]>;
    fn text_set(p: &mut Holder<str>, v: Owner<str>) -> ();
    fn text_get(p: &Holder<str>) -> Owner<str>;
    fn text_take(p: Holder<str>) -> Owner<str>;
    fn text_byval(p: Holder<str>, v: Owner<str>) -> Holder<str>;
    fn text_nested_set(p: &mut Outer<str>, v: Owner<str>) -> ();
    fn text_nested_get(p: &Outer<str>) -> Owner<str>;
    fn text_enum_set(p: &mut Choice<str>, v: Owner<str>) -> ();
    fn text_enum_get(p: &Choice<str>) -> Owner<str>;
    fn text_copy_pair(p: *mut Owner<str>, q: *const Owner<str>) -> ();
    fn text_replace(p: &mut Holder<str>, v: Owner<str>) -> Owner<str>;
    fn object_set(p: &mut Holder<dyn Eval>, v: Owner<dyn Eval>) -> ();
    fn object_get(p: &Holder<dyn Eval>) -> Owner<dyn Eval>;
    fn object_take(p: Holder<dyn Eval>) -> Owner<dyn Eval>;
    fn object_byval(p: Holder<dyn Eval>, v: Owner<dyn Eval>) -> Holder<dyn Eval>;
    fn object_nested_set(p: &mut Outer<dyn Eval>, v: Owner<dyn Eval>) -> ();
    fn object_nested_get(p: &Outer<dyn Eval>) -> Owner<dyn Eval>;
    fn object_enum_set(p: &mut Choice<dyn Eval>, v: Owner<dyn Eval>) -> ();
    fn object_enum_get(p: &Choice<dyn Eval>) -> Owner<dyn Eval>;
    fn object_copy_pair(p: *mut Owner<dyn Eval>, q: *const Owner<dyn Eval>) -> ();
    fn object_replace(p: &mut Holder<dyn Eval>, v: Owner<dyn Eval>) -> Owner<dyn Eval>;
}
fn check_slice(a: Owner<[u64]>, b: Owner<[u64]>, checks: &mut usize) {
    unsafe {
        assert_eq!(a.1.0.as_ptr() as *mut (), b.1.0.as_ptr() as *mut ());
        assert_eq!(
            std::ptr::metadata(a.1.0.as_ptr()),
            std::ptr::metadata(b.1.0.as_ptr())
        );
        assert_eq!(a.1.0.as_ref(), b.1.0.as_ref());
        *checks += 3;
    }
}
fn run_slice(old: Owner<[u64]>, new: Owner<[u64]>, seed: u64, checks: &mut usize) {
    unsafe {
        let mut v = old;
        slice_copy_pair(&mut v, &new);
        check_slice(v, new, checks);
        let p = core::ptr::addr_of_mut!(v);
        slice_copy_pair(p, p);
        check_slice(v, new, checks);
        let mut empty = Choice::Empty;
        slice_enum_set(&mut empty, new);
        assert!(matches!(empty, Choice::Empty));
        *checks += 1;
        let before = (seed ^ 0x65) as u8;
        let after = seed ^ 0xdeadbeef;
        let make = || Holder {
            before,
            item: old,
            after,
        };
        let check = |p: &Holder<[u64]>, checks: &mut usize| {
            assert_eq!(p.before, before);
            assert_eq!(p.after, after);
            *checks += 2;
            check_slice(p.item, new, checks);
        };
        let mut p = make();
        slice_set(&mut p, new);
        check(&p, checks);
        check_slice(slice_get(&p), new, checks);
        check_slice(slice_take(p), new, checks);
        let p = slice_byval(make(), new);
        check(&p, checks);
        let mut p = Outer {
            top: 0x4321,
            inner: make(),
            bottom: 0x87,
        };
        slice_nested_set(&mut p, new);
        assert_eq!(p.top, 0x4321);
        assert_eq!(p.bottom, 0x87);
        *checks += 2;
        check(&p.inner, checks);
        check_slice(slice_nested_get(&p), new, checks);
        let mut p = Choice::Some {
            before,
            item: old,
            after,
        };
        slice_enum_set(&mut p, new);
        if let Choice::Some {
            before: a,
            item,
            after: b,
        } = &p
        {
            assert_eq!(*a, before);
            assert_eq!(*b, after);
            *checks += 2;
            check_slice(*item, new, checks);
        } else {
            panic!("changed variant")
        }
        check_slice(slice_enum_get(&p), new, checks);
        let mut p = make();
        let previous = slice_replace(&mut p, new);
        check_slice(previous, old, checks);
        check(&p, checks);
    }
}
fn check_text(a: Owner<str>, b: Owner<str>, checks: &mut usize) {
    unsafe {
        assert_eq!(a.1.0.as_ptr() as *mut (), b.1.0.as_ptr() as *mut ());
        assert_eq!(
            std::ptr::metadata(a.1.0.as_ptr()),
            std::ptr::metadata(b.1.0.as_ptr())
        );
        assert_eq!(a.1.0.as_ref(), b.1.0.as_ref());
        *checks += 3;
    }
}
fn run_text(old: Owner<str>, new: Owner<str>, seed: u64, checks: &mut usize) {
    unsafe {
        let mut v = old;
        text_copy_pair(&mut v, &new);
        check_text(v, new, checks);
        let p = core::ptr::addr_of_mut!(v);
        text_copy_pair(p, p);
        check_text(v, new, checks);
        let mut empty = Choice::Empty;
        text_enum_set(&mut empty, new);
        assert!(matches!(empty, Choice::Empty));
        *checks += 1;
        let before = (seed ^ 0x65) as u8;
        let after = seed ^ 0xdeadbeef;
        let make = || Holder {
            before,
            item: old,
            after,
        };
        let check = |p: &Holder<str>, checks: &mut usize| {
            assert_eq!(p.before, before);
            assert_eq!(p.after, after);
            *checks += 2;
            check_text(p.item, new, checks);
        };
        let mut p = make();
        text_set(&mut p, new);
        check(&p, checks);
        check_text(text_get(&p), new, checks);
        check_text(text_take(p), new, checks);
        let p = text_byval(make(), new);
        check(&p, checks);
        let mut p = Outer {
            top: 0x4321,
            inner: make(),
            bottom: 0x87,
        };
        text_nested_set(&mut p, new);
        assert_eq!(p.top, 0x4321);
        assert_eq!(p.bottom, 0x87);
        *checks += 2;
        check(&p.inner, checks);
        check_text(text_nested_get(&p), new, checks);
        let mut p = Choice::Some {
            before,
            item: old,
            after,
        };
        text_enum_set(&mut p, new);
        if let Choice::Some {
            before: a,
            item,
            after: b,
        } = &p
        {
            assert_eq!(*a, before);
            assert_eq!(*b, after);
            *checks += 2;
            check_text(*item, new, checks);
        } else {
            panic!("changed variant")
        }
        check_text(text_enum_get(&p), new, checks);
        let mut p = make();
        let previous = text_replace(&mut p, new);
        check_text(previous, old, checks);
        check(&p, checks);
    }
}
fn check_object(a: Owner<dyn Eval>, b: Owner<dyn Eval>, checks: &mut usize) {
    unsafe {
        assert_eq!(a.1.0.as_ptr() as *mut (), b.1.0.as_ptr() as *mut ());
        assert_eq!(
            std::ptr::metadata(a.1.0.as_ptr()),
            std::ptr::metadata(b.1.0.as_ptr())
        );
        assert_eq!(a.1.0.as_ref().eval(), b.1.0.as_ref().eval());
        *checks += 3;
    }
}
fn run_object(old: Owner<dyn Eval>, new: Owner<dyn Eval>, seed: u64, checks: &mut usize) {
    unsafe {
        let mut v = old;
        object_copy_pair(&mut v, &new);
        check_object(v, new, checks);
        let p = core::ptr::addr_of_mut!(v);
        object_copy_pair(p, p);
        check_object(v, new, checks);
        let mut empty = Choice::Empty;
        object_enum_set(&mut empty, new);
        assert!(matches!(empty, Choice::Empty));
        *checks += 1;
        let before = (seed ^ 0x65) as u8;
        let after = seed ^ 0xdeadbeef;
        let make = || Holder {
            before,
            item: old,
            after,
        };
        let check = |p: &Holder<dyn Eval>, checks: &mut usize| {
            assert_eq!(p.before, before);
            assert_eq!(p.after, after);
            *checks += 2;
            check_object(p.item, new, checks);
        };
        let mut p = make();
        object_set(&mut p, new);
        check(&p, checks);
        check_object(object_get(&p), new, checks);
        check_object(object_take(p), new, checks);
        let p = object_byval(make(), new);
        check(&p, checks);
        let mut p = Outer {
            top: 0x4321,
            inner: make(),
            bottom: 0x87,
        };
        object_nested_set(&mut p, new);
        assert_eq!(p.top, 0x4321);
        assert_eq!(p.bottom, 0x87);
        *checks += 2;
        check(&p.inner, checks);
        check_object(object_nested_get(&p), new, checks);
        let mut p = Choice::Some {
            before,
            item: old,
            after,
        };
        object_enum_set(&mut p, new);
        if let Choice::Some {
            before: a,
            item,
            after: b,
        } = &p
        {
            assert_eq!(*a, before);
            assert_eq!(*b, after);
            *checks += 2;
            check_object(*item, new, checks);
        } else {
            panic!("changed variant")
        }
        check_object(object_enum_get(&p), new, checks);
        let mut p = make();
        let previous = object_replace(&mut p, new);
        check_object(previous, old, checks);
        check(&p, checks);
    }
}
fn owner<T: ?Sized>(p: NonNull<T>) -> Owner<T> {
    Owner((), Ptr(p), PhantomData)
}
fn main() {
    let mut checks = 0;
    for seed in 0..1024u64 {
        let n = seed.wrapping_mul(0x9876543219876543);
        let a = [
            n,
            n ^ 1,
            n.wrapping_add(2),
            !n,
            0,
            u64::MAX,
            n.rotate_left(17),
        ];
        let b = [n.rotate_left(9), n ^ 0xffff, n >> 7, 1, 22, 333, 4444];
        let al = (seed as usize) % 8;
        let bl = 7 - al;
        run_slice(
            owner(NonNull::from(&a[..al])),
            owner(NonNull::from(&b[..bl])),
            n,
            &mut checks,
        );
        let a = "aé中🦀z";
        let b = "different string";
        let a = if seed & 1 == 0 { a } else { "" };
        let b = if seed & 1 == 0 { "" } else { b };
        run_text(
            owner(NonNull::from(a)),
            owner(NonNull::from(b)),
            n,
            &mut checks,
        );
        let a = A(n);
        let b = B(!n);
        run_object(
            owner(NonNull::from(&a as &dyn Eval)),
            owner(NonNull::from(&b as &dyn Eval)),
            n,
            &mut checks,
        );
    }
    assert_eq!(checks, 150528);
    println!("PASS wide_projection checks={checks}");
}
