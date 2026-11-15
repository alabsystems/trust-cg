// CORPUS FIXTURE — the pointer / enum validity `AssertKind`s rustc's UB-check
// passes emit (compiled with `-Zub-checks=yes`, so they exist at every opt
// level) must, when they fail, call the exact NOUNWIND panic entry rustc's
// codegen calls — `panic_misaligned_pointer_dereference(required, found)`,
// `panic_null_pointer_dereference()`, `panic_null_reference_constructed()`,
// `panic_invalid_enum_construction(source)` — so the hook runs with rustc's own
// message (and payload) before the process aborts, under either strategy.
//
// `PANIC_SHAPE` works as in `panic_assert_kinds.rs` (`z` = no panic; a second
// byte `d` selects std's default hook). Every address involved is a fixed
// constant, so the payload printed by the default hook is deterministic.
use std::hint::black_box;

#[repr(u8)]
#[derive(Clone, Copy)]
#[allow(dead_code)]
enum Small {
    A = 1,
    B = 2,
    C = 3,
}

#[inline(never)]
fn misaligned_read(addr: usize) -> u64 {
    // The alignment check runs BEFORE the read, so the (unmapped) address is
    // never dereferenced.
    let p = addr as *const u32;
    unsafe { *p as u64 }
}

#[inline(never)]
fn null_read(p: *const u64) -> u64 {
    unsafe { *p }
}

#[inline(never)]
fn null_reference(p: *const u16) -> u64 {
    let r: &u16 = unsafe { &*p };
    black_box(r);
    7
}

/// A 128-bit discriminant: the invalid value's HIGH half reaches the message
/// only if the `u128` payload is passed whole.
#[repr(u128)]
#[derive(Clone, Copy)]
#[allow(dead_code)]
enum Wide {
    Lo = 5,
    Hi = 1 << 100,
}

#[inline(never)]
fn wide_enum_from(v: u128) -> u64 {
    let e: Wide = unsafe { std::mem::transmute::<u128, Wide>(v) };
    (e as u128 >> 64) as u64 ^ (e as u128 as u64)
}

#[inline(never)]
fn enum_from(v: u8) -> u64 {
    let e: Small = unsafe { std::mem::transmute::<u8, Small>(v) };
    e as u8 as u64
}

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

fn selector(at: usize) -> u8 {
    let value = unsafe { getenv(c"PANIC_SHAPE".as_ptr()) };
    if value.is_null() {
        return 0;
    }
    let first = unsafe { *value as u8 };
    if at == 0 || first == 0 {
        first
    } else {
        unsafe { *value.add(1) as u8 }
    }
}

fn main() {
    if selector(1) != b'd' {
        std::panic::set_hook(Box::new(|info| {
            let l = info.location().expect("a location");
            let code = (l.line() * 7 + l.column() * 3 + l.file().len() as u32) % 251;
            unsafe { write(1, b"hook\n".as_ptr(), 5) };
            std::process::exit(code as i32);
        }));
    }
    let word: u64 = black_box(0x1234_5678_9abc_def0);
    let half: u16 = black_box(77);
    let x = match selector(0) {
        b'a' => misaligned_read(black_box(0x1001)),
        b'b' => null_read(black_box(std::ptr::null())),
        b'c' => null_reference(black_box(std::ptr::null())),
        b'e' => enum_from(black_box(7)),
        b'f' => wide_enum_from(black_box(0x1234_5678_9abc_def0_0fed_cba9_8765_4321)),
        // No panic: the same functions on valid inputs.
        _ => {
            misaligned_read(black_box(&word as *const u64 as usize))
                ^ null_read(black_box(&word))
                ^ null_reference(black_box(&half))
                ^ enum_from(black_box(2))
                ^ wide_enum_from(black_box(1 << 100))
        }
    };
    std::process::exit((x % 200) as i32 + 1);
}
