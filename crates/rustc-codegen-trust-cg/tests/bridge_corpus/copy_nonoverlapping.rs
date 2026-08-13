// CORPUS FIXTURE — `core::ptr::copy_nonoverlapping` (the real memcpy intrinsic
// STATEMENT). Before this lowering it failed closed at every opt level
// ([TCG-MIR-UNSUPPORTED] StatementKind::Intrinsic copy_nonoverlapping is not
// modeled). For a SCALAR-leaf element type and a COMPILE-TIME-CONSTANT element
// count it now unrolls to `count` naturally aligned typed load+store pairs
// (dst[i] = src[i]), each an already-proven Load/Store — no new proof obligation.
//
// At O2/O3 the surrounding `as_ptr`/`as_mut_ptr` inline and the intrinsic lowers
// here -> correct. At -O0 the copy is a non-inlined `core::ptr::copy_nonoverlapping`
// library CALL; its wrapper body now lowers too (the runtime-count intrinsic ->
// libc memcpy, and its precondition's dead `ArgumentType` panic-format blocks are
// trapped), so this is correct at O0/O2/O3. See `copy_nonoverlapping_runtime.rs`
// for the runtime-count coverage.
//
// (a) full u32 array copy; (b) partial copy (count 2 of 4, tail untouched);
// (c) u8 byte copy. All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) full u32 array copy.
    let sa: [u32; 3] = [black_box(10), black_box(20), black_box(30)];
    let mut da: [u32; 3] = [black_box(0), black_box(0), black_box(0)];
    unsafe {
        core::ptr::copy_nonoverlapping(sa.as_ptr(), da.as_mut_ptr(), 3);
    }
    let ok_a = da[0] == 10 && da[1] == 20 && da[2] == 30;

    // (b) partial copy: only the first 2 of 4, leaving the tail untouched.
    let sb: [u32; 4] = [black_box(5), black_box(6), black_box(7), black_box(8)];
    let mut db: [u32; 4] = [black_box(1), black_box(1), black_box(1), black_box(1)];
    unsafe {
        core::ptr::copy_nonoverlapping(sb.as_ptr(), db.as_mut_ptr(), 2);
    }
    let ok_b = db[0] == 5 && db[1] == 6 && db[2] == 1 && db[3] == 1;

    // (c) u8 byte copy.
    let sc: [u8; 5] = [black_box(1), black_box(2), black_box(3), black_box(4), black_box(5)];
    let mut dc: [u8; 5] = [black_box(0); 5];
    unsafe {
        core::ptr::copy_nonoverlapping(sc.as_ptr(), dc.as_mut_ptr(), 5);
    }
    let ok_c = dc[0] == 1 && dc[4] == 5;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
