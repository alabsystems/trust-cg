#![no_std]
unsafe extern "C" {
    fn structural_record(id: u64);
}
unsafe extern "C-unwind" {
    fn structural_may_panic(id: u64);
}
struct Guard(u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            structural_record(self.0);
            structural_may_panic(self.0);
        }
    }
}
struct Pair {
    a: Guard,
    b: Guard,
}
struct Parent {
    id: u64,
    pair: Pair,
}
impl Drop for Parent {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            structural_record(self.id);
            structural_may_panic(self.id);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn structural_cleanup(mode: u64) {
    let _outer = Guard(4);
    let _parent = Parent {
        id: 1,
        pair: Pair {
            a: Guard(2),
            b: Guard(3),
        },
    };
    if mode == 0 {
        unsafe {
            structural_may_panic(0);
        }
    }
}
