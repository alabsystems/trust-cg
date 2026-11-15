// nonnull_holder_field.rs — a STRUCT carrying a `NonNull<[u8]>` field, built from a
// slotted (two-lane) parameter, read back two-lane through `&Holder` and through a
// by-value field copy into the return slot, with the stack poisoned (0x42..) before
// each call so an unwritten length lane cannot pass by coincidence. EXPECTED EXIT
// CODE: 77 on every lane (LLVM oracle and the bridge at O0, O2, O3). The 2026-09-22
// adversarial review predicted a one-lane field write here; measured: both lanes.
#![no_std]
#![no_main]
use core::hint::black_box as bb;
use core::ptr::NonNull;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
static BUF5: [u8; 5] = [1, 2, 3, 4, 5];
static BUF7: [u8; 7] = [4, 5, 6, 7, 8, 9, 10];
pub struct Holder { pub p: NonNull<[u8]>, pub n: u64 }
#[inline(never)] fn nn_from_ref(s: &[u8]) -> NonNull<[u8]> { NonNull::from_ref(s) }
#[inline(never)] fn nn_len(p: NonNull<[u8]>) -> usize { p.len() }
#[inline(never)] fn mk(p: NonNull<[u8]>, n: u64) -> Holder { Holder { p, n } }
#[inline(never)] fn get(h: &Holder) -> NonNull<[u8]> { h.p }
#[inline(never)] fn wrap(p: NonNull<[u8]>) -> NonNull<[u8]> { let h = Holder { p, n: 7 }; h.p }
#[inline(never)] fn poison() -> u64 { let a = [0x4242_4242_4242_4242u64; 8]; bb(a)[3] }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: &[u8] = bb(&BUF5[..]);
    let b: &[u8] = bb(&BUF7[..]);
    let _ = poison();
    let h = mk(nn_from_ref(a), 9);
    let x = nn_len(get(&h)) as i32; // 5
    let _ = poison();
    let y = nn_len(wrap(nn_from_ref(b))) as i32; // 7
    let z = h.n as i32; // 9
    (x * 100 + y * 10 + z) % 251 // 500+70+9 = 579 % 251 = 77
}
