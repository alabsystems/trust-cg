unsafe extern "C" {
    fn memory_loop_limit(data: *const u64, count: usize) -> *const u64;
}

#[repr(C)]
struct Cursor {
    position: *const u64,
    sum: u64,
    seen: usize,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn memory_loop_sum(data: *const u64, count: usize) -> u64 {
    let end = unsafe { memory_loop_limit(data, count) };
    let mut state = Cursor { position: data, sum: 0, seen: 0 };
    while state.position != end {
        state.sum = state.sum.wrapping_add(unsafe { *state.position });
        state.seen += 1;
        state.position = unsafe { state.position.add(1) };
    }
    state.sum ^ (state.seen as u64).wrapping_mul(0x101)
}
