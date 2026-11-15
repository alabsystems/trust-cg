// (o) S2 — the single-register BY-VALUE AGGREGATE ARGUMENT lane loaded 8 bytes
// whatever the aggregate's size was (`isel.rs` `select_aggregate_arg`,
// `ArgLocation::Reg`), so every aggregate narrower than 8 bytes read memory the
// object does not own. This row puts a 5-byte `#[repr(C)]` aggregate at the
// very END of a mapped page whose successor page is UNMAPPED, and passes it BY
// VALUE to an `#[inline(never)]` callee.
//
// WATCHED AND IT DID NOT FIRE — recorded here because the reason is the useful
// part. Measured at the pin (9da5e237), `-Copt-level=0`, this row's `main`
// disassembles to a byte-by-byte copy of the five bytes out of the mapping and
// into a FRAME SLOT, and only then the over-wide load:
//
//     ldrb w0, [x3]      ; ... five of these, mmap tail -> frame slot x1
//     strb w0, [x2]
//     ldr  x0, [x1]      ; <- the 8-byte read of a 5-byte object
//     bl   ...4sum5
//
// The bridge admits a by-value aggregate argument only when it is a WHOLE
// LOCAL ("only a whole aggregate local is lowered by value"), so the base
// register is always a frame address and the three bytes past the object are
// always mapped. The over-read is real at the machine level and is fixed, but
// no Rust source reaches it with an unmapped successor today. Keep the row: it
// pins the answer and it fires the day a by-value argument is forwarded from a
// place the caller does not own.
//
// After the fix the same site reads exactly five bytes, composed 4 + 1:
//
//     ldr  w1, [x0]
//     ldrb w1, [x0, #0x4]
//     lsl  x1, x0, #32
//     orr  x0, x2, x1
//
// Must print `15` and exit 0 under both backends at -O0 and -O2.
#[repr(C)]
#[derive(Clone, Copy)]
struct P5 {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
}

#[inline(never)]
fn sum5(s: P5) -> u32 {
    s.a as u32 + s.b as u32 + s.c as u32 + s.d as u32 + s.e as u32
}

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn getpagesize() -> i32;
}

fn main() {
    unsafe {
        let page = getpagesize() as usize;
        let base = mmap(
            core::ptr::null_mut(),
            page * 2,
            0x1 | 0x2,    // PROT_READ | PROT_WRITE
            0x1000 | 0x2, // MAP_ANON | MAP_PRIVATE  (Darwin)
            -1,
            0,
        );
        if base as isize == -1 || base.is_null() {
            println!("mmap-failed");
            return;
        }
        // Punch the hole: any read past the first page now faults.
        if munmap(base.add(page), page) != 0 {
            println!("munmap-failed");
            return;
        }
        let tail = base.add(page - 5) as *mut P5;
        (*tail) = P5 {
            a: 1,
            b: 2,
            c: 3,
            d: 4,
            e: 5,
        };
        println!("{}", sum5(*tail));
    }
}
