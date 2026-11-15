use std::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

#[inline(never)]
fn fail(kind: usize) {
    let _guard = Guard;
    match kind % 2 {
        0 => {
            let s = std::hint::black_box("abc");
            std::hint::black_box(&s[..std::hint::black_box(4)]);
        }
        _ => {
            let s = std::hint::black_box("é");
            std::hint::black_box(&s[..std::hint::black_box(1)]);
        }
    }
}

fn main() {
    for k in 0..16 {
        let panic = std::panic::catch_unwind(|| fail(k)).unwrap_err();
        let message = panic.downcast_ref::<String>().unwrap();
        assert!(message.contains(if k % 2 == 0 {
            "out of bounds"
        } else {
            "not a char boundary"
        }));
        assert_eq!(DROPS.load(Ordering::SeqCst), k + 1);
    }
    println!("PASS linked_core_unwind panics=16 drops=16");
}
