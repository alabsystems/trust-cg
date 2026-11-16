// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

pub struct Ids {
    pub id0: u64,
    pub id1: u64,
    pub trips: u64,
    pub flags: u64,
}
#[derive(Debug)]
pub enum R {
    Ok(u64, u32),
    Err(u8),
}
#[no_mangle]
#[inline(never)]
pub extern "C" fn probe_root(out_res: *mut R, out_ids: *mut Ids, idx: u64) {
    let ids = Ids {
        id0: idx * 3,
        id1: u64::MAX - idx,
        trips: idx & 1,
        flags: 1 << idx,
    };
    let r = if idx % 2 == 0 {
        R::Ok(idx, 7)
    } else {
        R::Err(idx as u8)
    };
    unsafe {
        out_res.write(r);
        out_ids.write(ids);
    }
}
fn main() {
    let mut acc = 0u64;
    for idx in 0u64..7 {
        let mut res_slot = std::mem::MaybeUninit::<R>::uninit();
        let mut ids_slot = std::mem::MaybeUninit::<Ids>::uninit();
        let (res, ids) = unsafe {
            probe_root(res_slot.as_mut_ptr(), ids_slot.as_mut_ptr(), idx);
            (res_slot.assume_init(), ids_slot.assume_init())
        };
        println!(
            "probe {idx}: ids=({},{}) trips={} flags={} ok={}",
            ids.id0,
            ids.id1,
            ids.trips,
            ids.flags,
            matches!(res, R::Ok(..))
        );
        acc = acc
            .wrapping_mul(31)
            .wrapping_add(ids.id0 ^ ids.id1 ^ ids.flags);
    }
    std::process::exit((acc % 251) as i32);
}
