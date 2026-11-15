#![no_std]
struct Cursor<'a> { next: core::ptr::NonNull<u8>, end: *const u8, marker: core::marker::PhantomData<&'a u8> }
struct Wrapper<'a> { cursor: Cursor<'a> }
#[inline(never)]
unsafe fn advance(cursor: &mut Cursor) -> u64 {
    let value = unsafe { *cursor.next.as_ptr() };
    cursor.next = unsafe { core::ptr::NonNull::new_unchecked(cursor.next.as_ptr().add(1)) };
    value as u64
}
#[inline(never)]
unsafe fn finish(wrapper: Wrapper, first: u64) -> u64 {
    first | ((unsafe { *wrapper.cursor.next.as_ptr() } as u64) << 8)
        | (((wrapper.cursor.end as usize).wrapping_sub(wrapper.cursor.next.as_ptr() as usize) as u64) << 16)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn projected_cursor(data: *const u8, len: usize) -> u64 {
    let mut wrapper = Wrapper { cursor: Cursor { next: unsafe { core::ptr::NonNull::new_unchecked(data as *mut u8) }, end: unsafe { data.add(len) }, marker: core::marker::PhantomData } };
    let first = unsafe { advance(&mut wrapper.cursor) };
    unsafe { finish(wrapper, first) }
}
