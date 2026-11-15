#![no_std]

// Only the selected helper is collected for each const instantiation. Keeping
// the other arms produces undefined generic symbols even though they cannot run.
#[inline(never)]
fn small<const N: usize>(x: u64) -> u64 {
    x.wrapping_add(N as u64 + 7)
}
#[inline(never)]
fn large<const N: usize>(x: u64) -> u64 {
    x.rotate_left(N as u32)
}
#[inline(never)]
fn middle<const N: usize>(x: u64) -> u64 {
    x ^ (N as u64).wrapping_mul(0x123456789)
}
#[inline(never)]
fn last<const N: usize>(x: u64) -> u64 {
    x.wrapping_mul(N as u64 + 3)
}

#[inline(never)]
fn choose<const N: usize>(x: u64, dynamic: bool) -> u64 {
    let value = match const { N % 3 } {
        0 => {
            if const { N < 3 } {
                small::<N>(x)
            } else {
                large::<N>(x)
            }
        }
        1 => middle::<N>(x),
        _ => last::<N>(x),
    };
    // Both dynamic arms must remain, including their independently compiled calls.
    if dynamic {
        runtime_left(value)
    } else {
        runtime_right(value)
    }
}
unsafe extern "Rust" {
    fn observe(value: u64, marker: u64) -> u64;
}
#[inline(never)]
fn runtime_left(value: u64) -> u64 {
    unsafe { observe(value, 17) }
}
#[inline(never)]
fn runtime_right(value: u64) -> u64 {
    unsafe { observe(value, 29) }
}

macro_rules! wrapper {
    ($name:ident, $n:literal) => {
        #[unsafe(no_mangle)]
        pub fn $name(value: u64, dynamic: bool) -> u64 {
            choose::<$n>(value, dynamic)
        }
    };
}
wrapper!(mono_0, 0);
wrapper!(mono_1, 1);
wrapper!(mono_2, 2);
wrapper!(mono_3, 3);
wrapper!(mono_4, 4);
wrapper!(mono_5, 5);
wrapper!(mono_63, 63);
wrapper!(mono_64, 64);

// Local inlining preserves the direct empty DropGlue call at O0. No helper may
// be emitted for it; live user destructors and reified drop functions still run.
#[inline(never)]
unsafe fn drop_pointer<T: ?Sized>(value: *mut T) {
    unsafe { core::ptr::drop_in_place(value) }
}
#[unsafe(no_mangle)]
pub unsafe fn mono_drop_word(value: *mut u64) {
    unsafe { drop_pointer(value) }
}
#[unsafe(no_mangle)]
pub unsafe fn mono_drop_slice(value: *mut [u32]) {
    unsafe { drop_pointer(value) }
}
#[unsafe(no_mangle)]
pub unsafe fn mono_drop_zst(value: *mut ()) {
    unsafe { drop_pointer(value) }
}
#[unsafe(no_mangle)]
pub fn mono_drop_fn() -> unsafe fn(*mut u64) {
    core::ptr::drop_in_place::<u64>
}

struct Guard(u64);
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { observe(self.0, 43) };
    }
}
#[unsafe(no_mangle)]
pub fn mono_live_drop(value: u64) {
    core::mem::drop(Guard(value));
}
