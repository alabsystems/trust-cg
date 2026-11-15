// CORPUS FIXTURE — a CELLED return place. `let res = ..; <borrow &res into a
// callee whose return carries a reference>; res` makes `res` the return place
// `_0` AND gives it a memory cell (`compute_scalar_cell_locals`), so every write
// lands in the cell and `return` must read the cell. The `Repr` shape is
// `library/core`'s `io::error::repr::Repr::new_custom` (its debug-assert
// `matches!(res.data(), ErrorData::Custom(_))`); `w` / `flag` / `wide` are the
// same class on a u64 newtype, a bool and a u128. Before: `[TCG-SSA-071] value
// ValueId(0) used in bbN is never defined`. Correct exit = LLVM oracle (4 at O0/O2/O3).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
use core::marker::PhantomData;
use core::ptr::NonNull;

pub enum Data<'a> {
    Os(i32),
    Custom(&'a u32),
}

#[repr(transparent)]
pub struct Repr(NonNull<()>, PhantomData<u32>);

impl Repr {
    #[inline(never)]
    pub fn data(&self) -> Data<'_> {
        let bits = self.0.as_ptr() as usize;
        if bits & 3 == 1 {
            Data::Custom(unsafe { &*((bits - 1) as *const u32) })
        } else {
            Data::Os(bits as i32)
        }
    }
    #[inline(never)]
    pub fn new_custom(b: NonNull<u32>) -> Self {
        let tagged = b.as_ptr().cast::<u8>().wrapping_add(1).cast::<()>();
        let res = Self(unsafe { NonNull::new_unchecked(tagged) }, PhantomData);
        if !matches!(res.data(), Data::Custom(_)) {
            panic!("repr(custom) encoding failed");
        }
        res
    }
}

#[repr(transparent)]
pub struct W(u64);
#[inline(never)]
pub fn view(w: &W) -> Option<&u64> { if w.0 != 0 { Some(&w.0) } else { None } }
#[inline(never)]
pub fn view_bool(b: &bool) -> Option<&bool> { if *b { Some(b) } else { None } }
#[inline(never)]
pub fn view_wide(b: &u128) -> Option<&u128> { if *b != 0 { Some(b) } else { None } }

#[inline(never)]
pub fn w(v: u64) -> W {
    let res = W(v.wrapping_mul(3));
    if view(&res).is_none() {
        panic!("zero");
    }
    res
}
#[inline(never)]
pub fn flag(v: u64) -> bool {
    let res = v > 10;
    let _ = bb(view_bool(&res).is_some());
    res
}
#[inline(never)]
pub fn wide(v: u64) -> u128 {
    let res = (v as u128) << 70 | 5;
    let _ = bb(view_wide(&res).is_some());
    res
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut x: u32 = bb(77);
    let r = Repr::new_custom(NonNull::from(&mut x));
    let a = match bb(r).data() {
        Data::Custom(v) => *v as u64,
        Data::Os(_) => 1,
    };
    let b = w(bb(14)).0;
    let c = flag(bb(11)) as u64 + 2 * flag(bb(3)) as u64;
    let d = wide(bb(9));
    ((a + b + c * 7 + ((d >> 70) as u64) * 11 + (d as u64 & 0xff)) % 113) as i32
}
