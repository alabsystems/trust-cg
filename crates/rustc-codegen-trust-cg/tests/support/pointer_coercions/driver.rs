use pointer_coercion_types::*;
use std::{
    marker::PhantomData,
    ptr::NonNull,
    rc::Rc,
    sync::{Arc, atomic::Ordering},
};
unsafe extern "Rust" {
    fn const_static() -> Ptr<[u64]>;
    fn ptr_via_call(v: Ptr<[u64; 7]>) -> Ptr<[u64]>;
    fn const_empty() -> Owner<[u8]>;
    fn ptr_slice(v: Ptr<[u64; 7]>) -> Ptr<[u64]>;
    fn ptr_empty(v: Ptr<[u64; 0]>) -> Ptr<[u64]>;
    fn ptr_zst(v: Ptr<[(); 17]>) -> Ptr<[()]>;
    fn nonnull_slice(v: NonNull<[u64; 7]>) -> NonNull<[u64]>;
    fn owner_slice(v: Owner<[u64; 7]>) -> Owner<[u64]>;
    fn tail_slice(v: Ptr<Tail<[u64; 7]>>) -> Ptr<Tail<[u64]>>;
    fn ptr_dyn(v: Ptr<Value>) -> Ptr<dyn Both + Send + Sync>;
    fn ptr_auto(v: Ptr<dyn Both + Send + Sync>) -> Ptr<dyn Both>;
    fn ptr_upcast(v: Ptr<dyn Both>) -> Ptr<dyn Right>;
    fn tail_dyn(v: Ptr<Tail<Value>>) -> Ptr<Tail<dyn Both>>;
    fn box_slice(v: Box<[u64; 7]>) -> Box<[u64]>;
    fn rc_slice(v: Rc<[u64; 7]>) -> Rc<[u64]>;
    fn arc_slice(v: Arc<[u64; 7]>) -> Arc<[u64]>;
    fn box_dyn(v: Box<Value>) -> Box<dyn Both>;
    fn rc_dyn(v: Rc<Value>) -> Rc<dyn Both>;
    fn arc_dyn(v: Arc<Value>) -> Arc<dyn Both>;
}
fn main() {
    let mut checks = 0;
    for seed in 0..1024u64 {
        unsafe {
            let n = seed.wrapping_mul(0x1234567812345679);
            let array = [
                n,
                n ^ 1,
                n.wrapping_add(2),
                !n,
                0,
                u64::MAX,
                n.rotate_left(17),
            ];
            let address = array.as_ptr();
            let p = const_static().0;
            assert_eq!(p.as_ptr() as *const u64, NUMS.as_ptr());
            assert_eq!(p.as_ref(), &NUMS);
            checks += 2;
            let p = ptr_via_call(Ptr(NonNull::from(&array))).0;
            assert_eq!(p.as_ptr() as *const u64, address);
            assert_eq!(p.as_ref(), &array);
            checks += 2;
            let p = const_empty().1;
            assert_eq!(
                p.as_ptr() as *mut u8,
                NonNull::<[u8; 0]>::dangling().as_ptr() as *mut u8
            );
            assert_eq!(p.len(), 0);
            checks += 2;
            let p = ptr_slice(Ptr(NonNull::from(&array))).0;
            assert_eq!(p.as_ptr() as *const u64, address);
            assert_eq!(p.as_ref(), &array);
            checks += 2;
            let empty: [u64; 0] = [];
            let p = ptr_empty(Ptr(NonNull::from(&empty))).0;
            assert_eq!(p.as_ptr() as *const u64, empty.as_ptr());
            assert_eq!(p.len(), 0);
            checks += 2;
            let zst = [(); 17];
            let p = ptr_zst(Ptr(NonNull::from(&zst))).0;
            assert_eq!(p.as_ptr() as *const (), zst.as_ptr());
            assert_eq!(p.len(), 17);
            checks += 2;
            let p = nonnull_slice(NonNull::from(&array));
            assert_eq!(p.as_ptr() as *const u64, address);
            assert_eq!(p.as_ref(), &array);
            checks += 2;
            let p = owner_slice(Owner(PhantomData, NonNull::from(&array), ())).1;
            assert_eq!(p.as_ptr() as *const u64, address);
            assert_eq!(p.as_ref(), &array);
            checks += 2;
            let tail = Tail {
                tag: n ^ 0xbeef,
                items: array,
            };
            let p = tail_slice(Ptr(NonNull::from(&tail))).0;
            assert_eq!(p.as_ptr() as *const (), &tail as *const _ as *const ());
            assert_eq!(p.as_ref().tag, tail.tag);
            assert_eq!(&p.as_ref().items, &array);
            checks += 3;
            let value = Value(n);
            let p = ptr_dyn(Ptr(NonNull::from(&value)));
            assert_eq!(p.0.as_ptr() as *const (), &value as *const _ as *const ());
            assert_eq!(p.0.as_ref().both(), value.both());
            checks += 2;
            let p = ptr_auto(p);
            assert_eq!(p.0.as_ptr() as *const (), &value as *const _ as *const ());
            assert_eq!(p.0.as_ref().left(), value.left());
            checks += 2;
            let p = ptr_upcast(p);
            assert_eq!(p.0.as_ptr() as *const (), &value as *const _ as *const ());
            assert_eq!(p.0.as_ref().right(), value.right());
            checks += 2;
            let tail = Tail {
                tag: n,
                items: Value(!n),
            };
            let p = tail_dyn(Ptr(NonNull::from(&tail))).0;
            assert_eq!(p.as_ptr() as *const (), &tail as *const _ as *const ());
            assert_eq!(p.as_ref().tag, n);
            assert_eq!(p.as_ref().items.both(), tail.items.both());
            checks += 3;
            let v = Box::new(array);
            let a = v.as_ptr();
            let p = box_slice(v);
            assert_eq!(p.as_ptr(), a);
            assert_eq!(&*p, &array);
            checks += 2;
            let v = Rc::new(array);
            let other = v.clone();
            let a = v.as_ptr();
            let p = rc_slice(v);
            assert_eq!(p.as_ptr(), a);
            assert_eq!(&*p, &array);
            assert_eq!(Rc::strong_count(&p), 2);
            drop(p);
            assert_eq!(Rc::strong_count(&other), 1);
            checks += 4;
            let v = Arc::new(array);
            let other = v.clone();
            let a = v.as_ptr();
            let p = arc_slice(v);
            assert_eq!(p.as_ptr(), a);
            assert_eq!(&*p, &array);
            assert_eq!(Arc::strong_count(&p), 2);
            drop(p);
            assert_eq!(Arc::strong_count(&other), 1);
            checks += 4;
            let before = DROPS.load(Ordering::Relaxed);
            let v = Box::new(Value(n));
            let a = &*v as *const _ as *const ();
            let p = box_dyn(v);
            assert_eq!(&*p as *const _ as *const (), a);
            assert_eq!(p.both(), value.both());
            drop(p);
            assert_eq!(DROPS.load(Ordering::Relaxed), before + 1);
            checks += 3;
            let before = DROPS.load(Ordering::Relaxed);
            let v = Rc::new(Value(n));
            let other = v.clone();
            let a = Rc::as_ptr(&v) as *const ();
            let p = rc_dyn(v);
            assert_eq!(Rc::as_ptr(&p) as *const (), a);
            assert_eq!(p.right(), value.right());
            assert_eq!(Rc::strong_count(&p), 2);
            drop(p);
            assert_eq!(DROPS.load(Ordering::Relaxed), before);
            drop(other);
            assert_eq!(DROPS.load(Ordering::Relaxed), before + 1);
            checks += 5;
            let before = DROPS.load(Ordering::Relaxed);
            let v = Arc::new(Value(n));
            let other = v.clone();
            let a = Arc::as_ptr(&v) as *const ();
            let p = arc_dyn(v);
            assert_eq!(Arc::as_ptr(&p) as *const (), a);
            assert_eq!(p.left(), value.left());
            assert_eq!(Arc::strong_count(&p), 2);
            drop(p);
            assert_eq!(DROPS.load(Ordering::Relaxed), before);
            drop(other);
            assert_eq!(DROPS.load(Ordering::Relaxed), before + 1);
            checks += 5;
        }
    }
    assert_eq!(checks, 52224);
    println!("PASS pointer_coercions checks={checks}");
}
