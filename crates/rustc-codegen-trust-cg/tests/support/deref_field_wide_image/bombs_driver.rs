use bombs::*;
use std::sync::atomic::Ordering;
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
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for &n in &[1usize, 3, 8] {
        for fuse in 0..=n {
            let before = DROPS.load(Ordering::SeqCst);
            let sum = DROP_SUM.load(Ordering::SeqCst);
            let b = (0..n).map(|i| Bomb(i, fuse)).collect::<Vec<_>>().into_boxed_slice();
            let caught = std::panic::catch_unwind(move || drop_bombs(b)).is_err();
            println!(
                "drop_bombs {n} fuse {fuse}: caught {caught} drops {} sum {}",
                DROPS.load(Ordering::SeqCst) - before,
                DROP_SUM.load(Ordering::SeqCst) - sum
            );
        }
    }
    report();
}
