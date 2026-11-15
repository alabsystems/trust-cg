//! Root-2 differential DRIVER: always compiled by LLVM. A size-checking global
//! allocator turns a wrong length lane of a field STORE into a printed BAD
//! DEALLOC (macOS free() ignores the size, so a wrong-size dealloc is otherwise
//! silent). The drop rows only show that `drop_glue::<Box<[T]>>` compiles and
//! frees correctly: its deref-led transmute's lanes are read by nothing yet
//! (the element needs no drop, and the free re-reads the box).
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering::SeqCst};
use subject::*;

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
static A: Checked = Checked;

fn bx(n: usize, seed: u8) -> Box<[u8]> { (0..n).map(|i| seed.wrapping_add(i as u8 * 7)).collect::<Vec<u8>>().into_boxed_slice() }
fn mk(s: &[u8]) -> Box<[u8]> { s.to_vec().into_boxed_slice() }
fn h(s: &[u8]) -> u64 { s.iter().fold(s.len() as u64, |a, &b| a.wrapping_mul(131).wrapping_add(b as u64)) }
fn show(row: &str, t: &W) { println!("{row}: tag {} n {} len {} h {}", t.tag, t.n, t.inner.len(), h(&t.inner)); }

fn main() {
    let lens = [0usize, 1, 7, 35];
    for &a in &lens { for &b in &lens {
        let mut t = W { tag: 0xA5, inner: bx(a, 1), n: 0xDEAD_BEEF };
        set_field(&mut t, bx(b, 9));
        show(&format!("set_field {a}->{b}"), &t);
        let mut o = Outer { a: 77, w: W { tag: 3, inner: bx(a, 2), n: 5 } };
        set_nested(&mut o, bx(b, 4));
        println!("set_nested {a}->{b}: a {} ", o.a); show("  w", &o.w);
        let old = replace_field(&mut t, bx(a, 6));
        println!("replace {a}<->{b}: old len {} h {}", old.len(), h(&old)); show("  t", &t);
        unsafe { set_raw(&mut t, bx(b, 8)); } show(&format!("set_raw {a}->{b}"), &t);
        let prev = unsafe { std::ptr::read(&t.inner) };
        unsafe { write_raw(&mut t, bx(a, 10)); } drop(prev); show(&format!("write_raw {b}->{a}"), &t);
        regrow(&mut t, &bx(b, 12), mk); show(&format!("regrow {a}->{b}"), &t);
        drop_box(bx(b, 14));
    }}
    let mut s = WS { k: 9, inner: "hello".into() };
    set_str(&mut s, "a longer replacement".into());
    println!("set_str: k {} {:?}", s.k, &*s.inner);
    let mut w = W64 { inner: vec![1u64, 2, 3].into_boxed_slice(), z: 42 };
    set_u64(&mut w, vec![10u64; 9].into_boxed_slice());
    println!("set_u64: z {} len {} sum {}", w.z, w.inner.len(), w.inner.iter().sum::<u64>());
    drop(s); drop(w);
    println!("allocs {} frees {} bad {}", ALLOCS.load(SeqCst), FREES.load(SeqCst), BAD.load(SeqCst));
    if BAD.load(SeqCst) { std::process::exit(3); }
}
