// The thin pointer swap ALONE: no reference is stored into an aggregate, so
// the stored-reference cell exclusion cannot raise the refusal first, and an
// excluded target must refuse with the swap's own text
// ("typed_swap_nonoverlapping over non-scalar"). `mem::swap` of `*const u32`
// and of `&u32`, each through `&mut` parameters.
#[no_mangle]
pub extern "C" fn cap_swap_raw(a: &mut *const u32, b: &mut *const u32) {
    core::mem::swap(a, b);
}
#[no_mangle]
pub extern "C" fn cap_swap_ref<'a>(a: &mut &'a u32, b: &mut &'a u32) -> u32 {
    core::mem::swap(a, b);
    **a ^ (**b).rotate_left(3)
}
