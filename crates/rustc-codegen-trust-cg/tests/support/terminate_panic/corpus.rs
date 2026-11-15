// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![no_std]

// Supply the actual linked Rust panic runtime metadata. These are ordinary
// source assertions and Drops, not hand-written panic entry declarations.
extern crate std;

unsafe extern "C" {
    fn terminate_panic_record_drop(id: u64);
}
unsafe extern "C-unwind" {
    fn terminate_panic_cleanup_callback(id: u64);
}

struct Guard(u64);

impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            terminate_panic_record_drop(self.0);
            terminate_panic_cleanup_callback(self.0);
        }
    }
}

pub const SOURCE_FILE: &str = file!();

// No Guard, no unrelated Cleanup edge, and no track_caller decoration: the
// source division Assert itself must stop unwinding at this C ABI boundary.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn terminate_source_boundary(numerator: u64, divisor: u64) -> u64 {
    numerator / divisor
}
pub const ABI_ASSERT_LINE: u32 = line!() - 2;
pub const ABI_ASSERT_COLUMN: u32 = 5;

// The first source panic unwinds through this live Guard. Its Drop callback
// can raise a second real Rust panic; the cleanup Drop edge must terminate
// with InCleanup, not reuse the C-boundary reason.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn terminate_source_cleanup(numerator: u64, divisor: u64) -> u64 {
    let _guard = Guard(7);
    numerator / divisor
}
pub const CLEANUP_ASSERT_LINE: u32 = line!() - 2;
pub const CLEANUP_ASSERT_COLUMN: u32 = 5;

// In an abort-built Rust body the foreign callback can still unwind. Its
// exception must run this live Guard's cleanup, then terminate at the Rust ABI
// boundary. The emitted source MIR must retain that entire path; treating all
// abort cleanup blocks as dead would silently lose the Drop or the abort.
#[cfg(terminate_foreign_object)]
#[unsafe(no_mangle)]
#[inline(never)]
pub fn terminate_source_foreign_guard(value: u64) -> u64 {
    let _guard = Guard(7);
    unsafe {
        terminate_panic_cleanup_callback(7);
    }
    value
}

// Ordinary C-unwind object exports are exclusive to the mixed-strategy lane. The
// original Rust rlib's roots and metadata linkage remain unchanged. Both
// signatures are also checked by a same-strategy, metadata-only Rust consumer.
#[cfg(terminate_foreign_object)]
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn terminate_foreign_drop_control(value: u64) -> u64 {
    terminate_source_cleanup(value, 7)
}

#[cfg(terminate_foreign_object)]
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn terminate_foreign_guard_control(value: u64) -> u64 {
    terminate_source_foreign_guard(value)
}
