#![no_std]
use core::marker::PhantomData;
use core::ptr::NonNull;
#[repr(C, align(8))]
pub struct Payload {
    pub bits: u64,
}
#[repr(transparent)]
struct Owner(NonNull<Payload>);
impl Drop for Owner {
    fn drop(&mut self) {}
}
impl Owner {
    #[inline(never)]
    fn into_raw(self) -> NonNull<Payload> {
        let ptr = self.0;
        core::mem::forget(self);
        ptr
    }
}
#[repr(transparent)]
struct Packed(NonNull<()>, PhantomData<Owner>);
enum Data<'a> {
    Number(u32),
    Custom(&'a Payload),
    Empty,
    Other,
}
impl Packed {
    #[inline(never)]
    fn data(&self) -> Data<'_> {
        let p = self.0.as_ptr().cast::<u8>();
        match p.addr() & 3 {
            0 => Data::Number(0),
            1 => Data::Custom(unsafe { &*p.wrapping_sub(1).cast::<Payload>() }),
            2 => Data::Empty,
            _ => Data::Other,
        }
    }
    #[inline(never)]
    fn new_custom(owner: Owner) -> Self {
        let p = owner.into_raw().as_ptr().cast::<u8>();
        debug_assert_eq!(p.addr() & 3, 0);
        let tagged = p.wrapping_add(1).cast::<()>();
        let ptr = unsafe { NonNull::new_unchecked(tagged) };
        let result = Self(ptr, PhantomData);
        debug_assert!(
            matches!(result.data(), Data::Custom(_)),
            "repr(custom) encoding failed"
        );
        result
    }
}
#[unsafe(no_mangle)]
pub unsafe fn packed_owner_address(p: *mut Payload) -> usize {
    let owner = Owner(unsafe { NonNull::new_unchecked(p) });
    Packed::new_custom(owner).0.as_ptr().addr()
}
