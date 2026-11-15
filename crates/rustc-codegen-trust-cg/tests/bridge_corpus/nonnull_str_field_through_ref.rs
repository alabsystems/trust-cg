// Fix B regression: scalar fields read THROUGH A REFERENCE to a struct whose
// first field is a `repr(transparent)` newtype over a `str` fat pointer
// (`NonNull<str>` = core's `panic::Location::filename`). The flattened
// by-reference pointee tuple collapsed that 16-byte field to ONE 8-byte `Ptr`
// lane, so every later field was read 8 bytes early: `Location::line()` returned
// the filename LENGTH and `column()` 0. `LocS` (a `&'static str` first field) is
// the control: that shape is already refused by the flattening
// ([TCG-FAT-POINTEE-LANE]) and read at rustc's offsets by the byte walker.
// CORPUS FIXTURE. Correct exit = LLVM oracle (68 at O0/O2/O3). Bridge before: exit=133 at
// O0, 118 at O2/O3 (a SILENT wrong value); after fix B: exit=68.
#![no_std]
#![no_main]
use core::hint::black_box;
use core::panic::Location;
use core::ptr::NonNull;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
pub struct LocS { f: &'static str, line: u32, col: u32 }
pub struct LocN { f: NonNull<str>, line: u32, col: u32 }
unsafe impl Sync for LocN {}
static A: LocS = LocS { f: "hello-world", line: 7, col: 9 };
static B: LocN = LocN { f: unsafe { NonNull::new_unchecked("abcdefghijklmnopqrstuvwxyz" as *const str as *mut str) }, line: 5, col: 3 };
static L: &Location<'static> = &Location::caller();
#[inline(never)] fn ref_s(l: &LocS) -> u32 { l.line * 100 + l.col }
#[inline(never)] fn ref_n(l: &LocN) -> u32 { l.line * 100 + l.col }
#[inline(never)] fn bor_n(l: &LocN) -> u32 { let p = &l.col; *p + 1 }
#[inline(never)] fn loc_lc(l: &Location<'static>) -> u32 { l.line() * 1000 + l.column() }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box(&A);
    let b = black_box(&B);
    let l = black_box(L);
    let acc = ref_s(a) + ref_n(b) * 3 + bor_n(b) * 5 + loc_lc(l) * 7;
    (acc % 251) as i32
}
