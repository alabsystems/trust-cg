use core::ptr::NonNull;
unsafe extern "C" {
    fn replace_slice(slot: *mut NonNull<[u32]>, data: *mut u32, len: usize);
}
#[repr(C)]
struct Guarded {
    before: u64,
    slot: NonNull<[u32]>,
    after: u64,
}
fn main() {
    let mut checks = 0;
    for len in 0..=16 {
        let old = [1u32; 3];
        let mut data = [27u32; 18];
        let mut g = Guarded {
            before: 0x1234,
            slot: NonNull::from(old.as_slice()),
            after: 0xabcd,
        };
        unsafe {
            replace_slice(&mut g.slot, data.as_mut_ptr().add(1), len);
        }
        let loaded = unsafe { g.slot.as_ref() };
        assert_eq!(loaded.len(), len);
        checks += 1;
        assert_eq!(loaded.as_ptr(), unsafe { data.as_ptr().add(1) });
        checks += 1;
        assert_eq!((g.before, g.after), (0x1234, 0xabcd));
        checks += 1;
        assert_eq!(data, [27u32; 18]);
        checks += 1;
    }
    println!("PASS wide_newtype_store checks={checks}");
}
