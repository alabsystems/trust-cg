use std::sync::atomic::Ordering;
use strings::*;
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
    for &n in &[0usize, 1, 3] {
        let mut ws = WStrings { k: 5, v: (0..n).map(|i| format!("s{i}")).collect::<Vec<_>>().into_boxed_slice() };
        set_strings(&mut ws, (0..n + 2).map(|i| "x".repeat(i)).collect::<Vec<_>>().into_boxed_slice());
        println!("set_strings {n}: k {} len {} total {}", ws.k, ws.v.len(), ws.v.iter().map(|s| s.len()).sum::<usize>());
        drop_strings((0..n).map(|i| i.to_string()).collect::<Vec<_>>().into_boxed_slice());
        drop(ws);
    }
    for &n in &[0usize, 1, 2, 7, 33] {
        let before = DROPS.load(Ordering::SeqCst);
        let sum = DROP_SUM.load(Ordering::SeqCst);
        drop_counted((0..n).map(|i| Counted(i * 3 + 1)).collect::<Vec<_>>().into_boxed_slice());
        println!(
            "drop_counted {n}: drops {} sum {}",
            DROPS.load(Ordering::SeqCst) - before,
            DROP_SUM.load(Ordering::SeqCst) - sum
        );
        drop_boxed_strs((0..n).map(|i| "ab".repeat(i).into_boxed_str()).collect::<Vec<_>>().into_boxed_slice());
        drop_vecs((0..n).map(|i| vec![i as u64; i]).collect::<Vec<_>>().into_boxed_slice());
    }
    report();
}
