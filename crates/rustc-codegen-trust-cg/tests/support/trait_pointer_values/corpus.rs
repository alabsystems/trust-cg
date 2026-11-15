#![no_std]

use core::ptr::NonNull;

pub trait ReadValue {
    fn read_value(&self, salt: u64) -> u64;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_ref_identity(value: &dyn ReadValue) -> &dyn ReadValue {
    value
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_mut_identity(value: &mut dyn ReadValue) -> &mut dyn ReadValue {
    value
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_raw_const(value: *mut dyn ReadValue) -> *const dyn ReadValue {
    value.cast_const()
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_raw_mut(value: *const dyn ReadValue) -> *mut dyn ReadValue {
    value.cast_mut()
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_nonnull_identity(value: NonNull<dyn ReadValue>) -> NonNull<dyn ReadValue> {
    value
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_nonnull_as_ptr(value: NonNull<dyn ReadValue>) -> *mut dyn ReadValue {
    value.as_ptr()
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_nonnull_from_ref(value: &mut dyn ReadValue) -> NonNull<dyn ReadValue + '_> {
    NonNull::from(value)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn dyn_nonnull_as_ref<'a>(value: NonNull<dyn ReadValue>) -> &'a dyn ReadValue {
    unsafe { value.as_ref() }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn dyn_nonnull_as_mut<'a>(mut value: NonNull<dyn ReadValue>) -> &'a mut dyn ReadValue {
    unsafe { value.as_mut() }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_select(
    mut value: *mut dyn ReadValue,
    left: *mut dyn ReadValue,
    right: *mut dyn ReadValue,
    steps: usize,
) -> *mut dyn ReadValue {
    for step in 0..steps {
        value = if step & 1 == 0 { left } else { right };
    }
    value
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dyn_indirect(
    function: fn(*mut dyn ReadValue) -> *const dyn ReadValue,
    value: *mut dyn ReadValue,
) -> *const dyn ReadValue {
    function(value)
}

#[repr(C)]
pub struct Plain {
    pub value: u64,
}

#[repr(C, align(16))]
pub struct Biased {
    pub value: u64,
    pub bias: u64,
    pub spare: [u64; 2],
}

impl ReadValue for Plain {
    #[inline(never)]
    fn read_value(&self, salt: u64) -> u64 {
        self.value.wrapping_add(salt)
    }
}

impl ReadValue for Biased {
    #[inline(never)]
    fn read_value(&self, salt: u64) -> u64 {
        self.value.wrapping_mul(3).wrapping_add(self.bias ^ salt)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn exercise_trait_pointers(
    first: *mut Plain,
    second: *mut Biased,
    salt: u64,
    pick: u32,
    mode: u32,
) -> u64 {
    let left: &mut (dyn ReadValue + 'static) = unsafe { &mut *first };
    let right: &mut (dyn ReadValue + 'static) = unsafe { &mut *second };
    let left_ptr = left as *mut dyn ReadValue;
    let right_ptr = right as *mut dyn ReadValue;
    let selected = if pick == 0 { left } else { right };
    match mode {
        0 => dyn_ref_identity(selected).read_value(salt),
        1 => dyn_mut_identity(selected).read_value(salt),
        2 => unsafe { (&*dyn_raw_const(selected)).read_value(salt) },
        3 => unsafe { (&*dyn_raw_mut(selected)).read_value(salt) },
        4 => {
            let pointer = unsafe { NonNull::new_unchecked(selected as *mut dyn ReadValue) };
            let pointer = dyn_nonnull_identity(pointer);
            unsafe { pointer.as_ref() }.read_value(salt)
        }
        5 => {
            let pointer = unsafe { NonNull::new_unchecked(selected as *mut dyn ReadValue) };
            unsafe { (&*dyn_nonnull_as_ptr(pointer)).read_value(salt) }
        }
        6 => unsafe { dyn_nonnull_from_ref(selected).as_ref() }.read_value(salt),
        7 => {
            let pointer = unsafe { NonNull::new_unchecked(selected as *mut dyn ReadValue) };
            let pointer = dyn_nonnull_as_ptr(dyn_nonnull_identity(pointer));
            let data = pointer as *mut u64;
            unsafe { *data = (*data).wrapping_add(salt) };
            unsafe { (&*pointer).read_value(salt) }
        }
        8 => core::mem::size_of_val(dyn_ref_identity(selected)) as u64,
        9 => core::mem::align_of_val(dyn_ref_identity(selected)) as u64,
        10 => {
            let pointer = unsafe { NonNull::new_unchecked(selected as *mut dyn ReadValue) };
            unsafe { dyn_nonnull_as_ref(pointer) }.read_value(salt)
        }
        11 => {
            let pointer = unsafe { NonNull::new_unchecked(selected as *mut dyn ReadValue) };
            unsafe { dyn_nonnull_as_mut(pointer) }.read_value(salt)
        }
        12 => {
            let pointer = dyn_select(selected, left_ptr, right_ptr, (salt & 7) as usize);
            unsafe { (&*pointer).read_value(salt) }
        }
        13 => unsafe { (&*dyn_indirect(dyn_raw_const, selected)).read_value(salt) },
        _ => u64::MAX,
    }
}
