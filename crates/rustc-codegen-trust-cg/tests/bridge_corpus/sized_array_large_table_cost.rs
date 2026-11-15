// CORPUS FIXTURE — the SIZE-CLIFF control for the sized-array lane.
//
// THE QUESTION THIS ANSWERS. Mapping `[T; N]` field-wise is O(N) in compiler
// time and memory (`aggregate_reference_pointee_to_trust_ir_ty`'s array arm
// builds one leaf PER ELEMENT, which for `[u8; 4 << 20]` measured 640MB RSS and
// 2.0s against LLVM's 98MB / 0.11s). The widened pointee arm this lane adds
// moves array pointees the flattening CANNOT represent onto the MEMORY-SLOT
// spelling instead, which is `Ty::Array(lane, n)` built in O(1) by
// `memory_slot_lane_ty` and whose leaf validation short-circuits a uniform array
// (`validate_memory_aggregate_field_leaves`'s `FieldsShape::Array` arm). So the
// widening moves work OFF the O(N) spelling and never onto it, and no new size
// bound is introduced — this row is the measurement that says so, at a table
// size (8192 x 8 bytes = 64 KiB, spelled as 32768 I16 lanes) two orders of
// magnitude above anything `library/core` holds.
//
// It is also a VALUE check: the elements read back are position-dependent, so a
// stride taken from the register width rather than `size_of::<(u16,[u16;3])>()`
// diverges from LLVM here rather than merely being slow.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
use core::hint::black_box as bb;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

fn put(v: u32) {
    let mut b = [0u8; 12];
    let mut i = 11usize;
    b[11] = b'\n';
    let mut x = v;
    loop {
        i -= 1;
        b[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    unsafe {
        write(1, b.as_ptr().wrapping_add(i), 12 - i);
    }
}

const N: usize = 8192;

static BIG: [(u16, [u16; 3]); N] = {
    let mut t = [(0u16, [0u16; 3]); N];
    let mut i = 0usize;
    while i < N {
        let k = (i as u16).wrapping_mul(7).wrapping_add(1);
        t[i] = (k, [k ^ 0x1111, k ^ 0x2222, k ^ 0x3333]);
        i += 1;
    }
    t
};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let t: &[(u16, [u16; 3])] = &BIG;
    let mut acc: u32 = 0;
    // Sample across the whole table, including the last element, so a wrong
    // stride cannot stay inside the first page.
    let probes: [usize; 8] = [0, 1, 2, 127, 1000, 4095, 8190, 8191];
    let mut p = bb(0usize);
    while p < 8 {
        let e = unsafe { t.get_unchecked(probes[p]) };
        put(e.0 as u32);
        put(e.1[0] as u32);
        put(e.1[1] as u32);
        put(e.1[2] as u32);
        acc = acc.wrapping_mul(31).wrapping_add(e.0 as u32);
        acc = acc.wrapping_mul(31).wrapping_add(e.1[0] as u32);
        acc = acc.wrapping_mul(31).wrapping_add(e.1[1] as u32);
        acc = acc.wrapping_mul(31).wrapping_add(e.1[2] as u32);
        p += 1;
    }
    put(acc % 1000);
    (acc % 79) as i32
}
