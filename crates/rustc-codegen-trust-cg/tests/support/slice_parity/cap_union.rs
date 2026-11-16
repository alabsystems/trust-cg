use core::mem::MaybeUninit;
pub struct Ids {
    pub id0: u64,
    pub id1: u64,
    pub trips: u32,
    pub flags: u8,
}
#[inline(never)]
fn fill(out: *mut Ids, idx: u64) {
    unsafe {
        out.write(Ids {
            id0: idx * 3,
            id1: !idx,
            trips: idx as u32,
            flags: idx as u8,
        })
    }
}
#[no_mangle]
pub extern "C" fn cap_union(idx: u64) -> u64 {
    let mut s = MaybeUninit::<Ids>::uninit();
    fill(s.as_mut_ptr(), idx);
    let i = unsafe { s.assume_init() };
    i.id0 ^ i.id1 ^ i.trips as u64 ^ i.flags as u64
}
