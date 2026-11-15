// CORPUS FIXTURE — `vec![x; n]` and `repeat(n)` whose element extent cannot be
// allocated raise std's capacity-overflow panic ("capacity overflow", from
// alloc's `raw_vec` or `<[T]>::repeat`'s `checked_mul(..).expect(..)`), and
// the raise takes the source call's own unwind edge: a live guard's Drop runs
// (cleanup edge), an `extern "C"` frame aborts with "panic in a function that
// cannot unwind" (terminate edge), a plain frame unwinds to `lang_start`.
// Uppercase rows run the same frames with a small count (the controls).
// Before the fix the bridge refused every `panic=unwind` build of this fixture
// by name ("unsupported capacity-overflow edge Terminate(Abi)").
struct Guard(u64);
impl Drop for Guard {
    fn drop(&mut self) {
        let id = self.0;
        println!("guard {id} dropped");
    }
}
unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}
fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}
#[inline(never)]
fn a_from_elem_guard(n: usize) -> u64 {
    let _g = Guard(1);
    let v = vec![7u64; n];
    v[0]
}
#[inline(never)]
fn b_repeat_guard(n: usize) -> u64 {
    let _g = Guard(2);
    let v = [1u8, 2].repeat(n);
    v[0] as u64
}
#[inline(never)]
extern "C" fn c_from_elem_nounwind(n: usize) -> u64 {
    let v = vec![7u64; n];
    v[0]
}
#[inline(never)]
extern "C" fn d_repeat_nounwind(n: usize) -> u64 {
    let v = [1u8, 2].repeat(n);
    v[0] as u64
}
#[inline(never)]
fn e_vec_deref_repeat(n: usize) -> u64 {
    let base: Vec<u16> = vec![1, 2, 3];
    let v = base.repeat(n);
    v[0] as u64
}
#[inline(never)]
fn f_string_repeat(n: usize) -> u64 {
    let s = String::from("abcd");
    let r = s.repeat(n);
    r.as_bytes()[0] as u64
}
#[inline(never)]
fn g_repeat_guard_mul(n: usize) -> u64 {
    let _g = Guard(7);
    let v = [1u32, 2, 3].repeat(n);
    v[0] as u64
}
fn main() {
    let w = shape();
    println!("start {w}");
    let z = (w as usize) & 0;
    let big = usize::MAX / 2 + 2 + z;
    let r = match w {
        b'a' => a_from_elem_guard((1usize << 61) + 1 + z),
        b'b' => b_repeat_guard(big),
        b'c' => c_from_elem_nounwind((1usize << 61) + 1 + z),
        b'd' => d_repeat_nounwind(big),
        b'e' => e_vec_deref_repeat(usize::MAX / 3 + 1 + z),
        b'f' => f_string_repeat(usize::MAX / 4 + 1 + z),
        b'g' => g_repeat_guard_mul(usize::MAX / 3 + 1 + z),
        b'A' => a_from_elem_guard(3 + z),
        b'B' => b_repeat_guard(3 + z),
        b'C' => c_from_elem_nounwind(3 + z),
        b'D' => d_repeat_nounwind(3 + z),
        b'E' => e_vec_deref_repeat(3 + z),
        b'F' => f_string_repeat(3 + z),
        b'G' => g_repeat_guard_mul(3 + z),
        _ => 0,
    };
    println!("r = {r}");
}
