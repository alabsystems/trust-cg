// CORPUS FIXTURE — `Option::take()` / `Option::replace()` / `mem::replace` on an
// enum carried across a loop. This is the `mem::replace` shape: the value is read
// out into a temp, the slot is overwritten in place, then the OLD temp is matched:
//
//   _t = Option::Some(..);     // build the replacement
//   _old = copy _cur;          // read the old value out
//   _cur = move _t;            // replace in place
//   _disc = discriminant(_old);// match the OLD value
//
// The loop-carried `_cur` is memory-backed (a runtime tag in a stack slot, via the
// multi-block enum case). A whole-enum copy can only be lowered when BOTH ends share
// a representation, so the read-out temp `_old` and the construct temp `_t` are
// memory-backed too (compute_memory_backed_locals propagates memory-backing across a
// whole-enum copy in both directions). Before that, the take/replace pattern failed
// closed ("ADT Use source discriminant before aggregate binding" /
// "memory aggregate whole assignment from non-memory source").
//
// Checks the family end to end at O2/O3 (O0 fails closed on the range-iterator
// library helper, an orthogonal gap): (a) take()-in-loop re-inserting a decremented
// value, (b) Option::replace returning the previous, (c) a Result<i32,i32>
// mem::replace exercising both arms. All correct -> exit 7. (O0: fail-closed note.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::mem;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) take() in a while-loop, re-inserting v-1: drains 5,4,3 -> sum 12.
    let mut cur: Option<i32> = Some(black_box(5));
    let mut sum = 0i32;
    let mut i = 0i32;
    while i < black_box(3) {
        if let Some(v) = cur.take() {
            sum += v;
            cur = Some(v - 1);
        }
        i += 1;
    }
    let ok_take = sum == 12;

    // (b) Option::replace returns the previous value: old chain 1,0,1 -> 2.
    let mut slot: Option<i32> = Some(black_box(1));
    let mut acc = 0i32;
    let mut j = 0i32;
    while j < black_box(3) {
        if let Some(old) = slot.replace(j) {
            acc += old;
        }
        j += 1;
    }
    let ok_replace = acc == 2;

    // (c) Result mem::replace, both arms: Ok(10) then Err(0),Ok(1) -> 10 - 0 + ... ,
    // here old = Ok(10), Err? exercise: replace with Err(k) each step.
    let mut r: Result<i32, i32> = Ok(black_box(10));
    let mut rsum = 0i32;
    let mut k = 0i32;
    while k < black_box(2) {
        match mem::replace(&mut r, Err(k)) {
            Ok(v) => rsum += v,
            Err(e) => rsum -= e,
        }
        k += 1;
    }
    // step0: old=Ok(10) -> +10, r=Err(0); step1: old=Err(0) -> -0, r=Err(1). rsum=10.
    let ok_result = rsum == 10;

    if ok_take && ok_replace && ok_result {
        7
    } else {
        13
    }
}
