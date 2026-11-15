#![no_std]
unsafe extern "C" {
    fn associated_record(id: u64);
}
unsafe extern "C-unwind" {
    fn associated_may_panic(id: u64);
}
struct Guard(u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            associated_record(self.0);
            associated_may_panic(self.0);
        }
    }
}
struct Pair {
    a: Guard,
    b: Guard,
}
trait Family {
    type Owned;
}
struct Kind;
impl Family for Kind {
    type Owned = Pair;
}
struct Parent<T: Family> {
    id: u64,
    pair: T::Owned,
}
impl<T: Family> Drop for Parent<T> {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            associated_record(self.id);
            associated_may_panic(self.id);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn associated_cleanup(mode: u64) {
    let _outer = Guard(4);
    let _parent = Parent::<Kind> {
        id: 1,
        pair: Pair {
            a: Guard(2),
            b: Guard(3),
        },
    };
    if mode == 0 {
        unsafe {
            associated_may_panic(0);
        }
    }
}
