use kinds::*;
// A size-checking global allocator: a free of an unknown pointer, or with a
// size or alignment other than the allocation's, sets BAD and the run exits 3.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering::SeqCst};

const N: usize = 4096;
struct Checked;
static PTRS: [AtomicUsize; N] = [const { AtomicUsize::new(0) }; N];
static SIZES: [AtomicUsize; N] = [const { AtomicUsize::new(0) }; N];
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
static BAD: AtomicBool = AtomicBool::new(false);
unsafe impl GlobalAlloc for Checked {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        ALLOCS.fetch_add(1, SeqCst);
        for i in 0..N {
            if PTRS[i].compare_exchange(0, p as usize, SeqCst, SeqCst).is_ok() {
                SIZES[i].store(l.size() | (l.align() << 48), SeqCst);
                return p;
            }
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        FREES.fetch_add(1, SeqCst);
        let mut found = false;
        for i in 0..N {
            if PTRS[i].load(SeqCst) == p as usize {
                if SIZES[i].load(SeqCst) != (l.size() | (l.align() << 48)) { BAD.store(true, SeqCst); }
                PTRS[i].store(0, SeqCst);
                found = true;
                break;
            }
        }
        if !found { BAD.store(true, SeqCst); }
        unsafe { System.dealloc(p, l) }
    }
}
#[global_allocator]
static GA: Checked = Checked;
fn report() {
    println!("allocs {} frees {} bad {}", ALLOCS.load(SeqCst), FREES.load(SeqCst), BAD.load(SeqCst));
    if BAD.load(SeqCst) { std::process::exit(3); }
}
use std::ptr::NonNull;
use std::rc::Rc;
fn h(s: &[u8]) -> u64 { s.iter().fold(s.len() as u64, |a, &b| a.wrapping_mul(131).wrapping_add(b as u64)) }
static A: [u16; 5] = [1, 2, 3, 4, 5];
static B: [u16; 2] = [9, 8];
fn main() {
    let mut t = Sl { a: 1, s: &A, b: 7 };
    set_slice(&mut t, &B);
    println!("slice a {} b {} {:?}", t.a, t.b, t.s);
    let mut buf = [5u8, 6, 7, 8];
    let mut n = Nn { a: 3, p: NonNull::from(&mut buf[..2]), b: 4 };
    set_nonnull(&mut n, NonNull::from(&mut buf[1..]));
    println!("nonnull a {} b {} {:?}", n.a, n.b, unsafe { n.p.as_ref() });
    let k = 11u64;
    let mut d = Dy { a: 1, d: Box::new(|x| x + 1), b: 2 };
    set_dyn(&mut d, Box::new(move |x| x * k));
    println!("dyn a {} b {} {}", d.a, d.b, (d.d)(6));
    let mut r = Rcs { a: 1, r: Rc::from(&[1u8, 2][..]), s: "x".into(), b: 2 };
    let keep: Rc<[u8]> = Rc::from(&[3u8, 4, 5][..]);
    set_rc(&mut r, keep.clone(), "hello".into());
    println!("rc a {} b {} {} {} {}", r.a, r.b, h(&r.r), &*r.s, Rc::strong_count(&keep));
    let mut o = Opt { a: 1, o: None, b: 2 };
    set_opt(&mut o, Some(vec![1u8, 2, 3].into_boxed_slice()));
    set_opt(&mut o, Some(vec![4u8; 9].into_boxed_slice()));
    println!("opt a {} b {} {:?}", o.a, o.b, o.o.as_deref().map(h));
    let mut p = Pair { a: 1, w: (vec![1u8].into_boxed_slice(), 5), b: 2 };
    set_pair(&mut p, (vec![7u8; 12].into_boxed_slice(), 9));
    println!("pair a {} b {} {} {}", p.a, p.b, h(&p.w.0), p.w.1);
    let mut ow = OuterK { a: 7, w: Inner { tag: 1, b: vec![2u8; 3].into_boxed_slice(), n: 4 }, z: 9 };
    set_w(&mut ow, Inner { tag: 5, b: vec![6u8; 17].into_boxed_slice(), n: 8 });
    println!("whole a {} z {} tag {} n {} {}", ow.a, ow.z, ow.w.tag, ow.w.n, h(&ow.w.b));
    drop((t, n, d, r, keep, o, p, ow));
    report();
}
