#![no_std]

pub trait Root {
    fn root(&self, salt: u64) -> u64;
}
pub trait Left: Root {
    fn left(&self, salt: u64) -> u64;
}
pub trait Right: Root {
    fn right(&self, salt: u64) -> u64;
    fn bump(&mut self, salt: u64) -> u64;
}
pub trait Top: Left + Right {
    fn top(&self, salt: u64) -> u64;
}
pub trait Extra {
    fn extra(&self, salt: u64) -> u64;
}
pub trait Super: Extra + Top {}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_left(value: &dyn Top) -> &dyn Left {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_right(value: &dyn Top) -> &dyn Right {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_root(value: &dyn Top) -> &dyn Root {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_top(value: &dyn Super) -> &dyn Top {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_super_right(value: &dyn Super) -> &dyn Right {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_raw(value: *mut dyn Super) -> *mut dyn Right {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_const(value: *const dyn Top) -> *const dyn Right {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_mut_top(value: &mut dyn Super) -> &mut dyn Top {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_mut_right(value: &mut dyn Top) -> &mut dyn Right {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn erase_principal(value: &(dyn Super + Send)) -> &dyn Send {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn erase_send(value: &(dyn Super + Send)) -> &dyn Super {
    value
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_indirect(
    function: fn(*mut dyn Super) -> *mut dyn Right,
    value: *mut dyn Super,
) -> *mut dyn Right {
    function(value)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn upcast_select(
    mut value: *mut dyn Super,
    left: *mut dyn Super,
    right: *mut dyn Super,
    steps: usize,
) -> *mut dyn Right {
    for step in 0..steps {
        value = if step & 1 == 0 { left } else { right };
    }
    value
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

macro_rules! methods {
    ($ty:ty, $bias:expr, $bump:expr) => {
        impl Root for $ty {
            #[inline(never)]
            fn root(&self, salt: u64) -> u64 {
                self.value.wrapping_add(salt).wrapping_add(11)
            }
        }
        impl Left for $ty {
            #[inline(never)]
            fn left(&self, salt: u64) -> u64 {
                self.value.wrapping_mul(3) ^ salt
            }
        }
        impl Right for $ty {
            #[inline(never)]
            fn right(&self, salt: u64) -> u64 {
                self.value
                    .wrapping_mul(5)
                    .wrapping_add(($bias)(self) ^ salt)
                    .wrapping_add(17)
            }
            #[inline(never)]
            fn bump(&mut self, salt: u64) -> u64 {
                self.value = self.value.wrapping_add(salt).wrapping_add($bump);
                self.right(salt)
            }
        }
        impl Top for $ty {
            #[inline(never)]
            fn top(&self, salt: u64) -> u64 {
                self.value.wrapping_mul(7).wrapping_sub(salt)
            }
        }
        impl Extra for $ty {
            #[inline(never)]
            fn extra(&self, salt: u64) -> u64 {
                self.value.wrapping_mul(13).wrapping_add(salt)
            }
        }
        impl Super for $ty {}
    };
}
methods!(Plain, |_: &Plain| 0u64, 19);
methods!(Biased, |value: &Biased| value.bias, 23);

#[unsafe(no_mangle)]
pub unsafe extern "C" fn exercise_upcasts(
    first: *mut Plain,
    second: *mut Biased,
    salt: u64,
    pick: u32,
    mode: u32,
) -> u64 {
    let left: &mut (dyn Super + Send) = unsafe { &mut *first };
    let right: &mut (dyn Super + Send) = unsafe { &mut *second };
    let left_ptr = left as *mut dyn Super;
    let right_ptr = right as *mut dyn Super;
    let selected = if pick == 0 { left } else { right };
    match mode {
        0 => upcast_top(selected).top(salt),
        1 => upcast_left(upcast_top(selected)).left(salt),
        2 => upcast_right(upcast_top(selected)).right(salt),
        3 => upcast_root(upcast_top(selected)).root(salt),
        4 => upcast_super_right(selected).right(salt),
        5 => unsafe { (&*upcast_raw(selected)).right(salt) },
        6 => upcast_mut_right(upcast_mut_top(selected)).bump(salt),
        7 => upcast_raw(selected) as *mut u8 as u64,
        8 => core::mem::size_of_val(upcast_super_right(selected)) as u64,
        9 => core::mem::align_of_val(upcast_super_right(selected)) as u64,
        10 => core::mem::size_of_val(erase_principal(selected)) as u64,
        11 => upcast_super_right(erase_send(selected)).right(salt),
        12 => unsafe { (&*upcast_const(upcast_top(selected))).right(salt) },
        13 => {
            let pointer = upcast_select(selected, left_ptr, right_ptr, (salt & 7) as usize);
            unsafe { (&*pointer).right(salt) }
        }
        14 => unsafe { (&*upcast_indirect(upcast_raw, selected)).right(salt) },
        15 => selected.extra(salt),
        _ => u64::MAX,
    }
}
