#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn memory_loop_limit(data: *const u64, count: usize) -> *const u64 {
    unsafe { data.add(count) }
}
