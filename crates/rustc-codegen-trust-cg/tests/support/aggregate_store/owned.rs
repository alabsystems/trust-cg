#![no_std]
unsafe extern "C" {
    fn store_allocate(id: u64, value: u64) -> *mut u64;
    fn store_release(ptr: *mut u64, id: u64);
    fn store_event(id: u64, value: u64);
}
unsafe extern "C-unwind" {
    fn store_may_panic(id: u64);
}
struct Leaf {
    ptr: *mut u64,
    id: u64,
}
impl Drop for Leaf {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            store_release(self.ptr, self.id);
            store_may_panic(self.id)
        }
    }
}
struct Owner {
    first: Leaf,
    words: [u64; 3],
    last: Leaf,
}
struct Guard;
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { store_event(90, 0) }
    }
}
#[inline(never)]
fn make(v: u64, id: u64) -> Owner {
    Owner {
        first: Leaf {
            ptr: unsafe { store_allocate(id, v) },
            id,
        },
        words: [v, v.rotate_left(17), !v],
        last: Leaf {
            ptr: unsafe { store_allocate(id + 1, !v) },
            id: id + 1,
        },
    }
}
#[inline(never)]
fn assign(dst: &mut Owner, src: Owner) {
    *dst = src;
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn store_owned(v: u64, replace: bool) {
    let _guard = Guard;
    let mut dst = make(v, 10);
    let src = make(v ^ 0x123456789, 20);
    if replace {
        let old = core::mem::replace(&mut dst, src);
        unsafe {
            store_event(30, old.words[0] ^ old.words[1] ^ old.words[2]);
        }
        drop(old);
    } else {
        assign(&mut dst, src);
    }
    unsafe {
        store_event(40, dst.words[0] ^ dst.words[1] ^ dst.words[2]);
    }
}
