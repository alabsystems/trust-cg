// The `core::fmt::rt::ArgumentType` SHAPE, rebuilt in a user crate: a two-variant
// enum whose first variant carries a non-null data pointer plus a function
// pointer (so the layout is NICHE-encoded in the pointer) and whose second
// variant carries a u16. This is the memory layout the self-host lane now asks
// rustc for when `core` is compiled by this backend.
use core::marker::PhantomData;
use core::ptr::NonNull;

#[derive(Copy, Clone)]
enum ArgTy<'a> {
    Placeholder {
        value: NonNull<()>,
        formatter: unsafe fn(NonNull<()>) -> u64,
        _lifetime: PhantomData<&'a ()>,
    },
    Count(u16),
}

unsafe fn show_i32(p: NonNull<()>) -> u64 {
    let r: &i32 = unsafe { &*(p.as_ptr() as *const i32) };
    (*r as i64 as u64).wrapping_mul(3)
}

unsafe fn show_u8(p: NonNull<()>) -> u64 {
    let r: &u8 = unsafe { &*(p.as_ptr() as *const u8) };
    (*r as u64).wrapping_add(1000)
}

fn eval(a: ArgTy<'_>) -> u64 {
    match a {
        ArgTy::Placeholder { value, formatter, .. } => unsafe { formatter(value) },
        ArgTy::Count(n) => n as u64,
    }
}

fn main() {
    let x: i32 = -7;
    let y: u8 = 9;
    let p1 = ArgTy::Placeholder {
        value: NonNull::from(&x).cast::<()>(),
        formatter: show_i32,
        _lifetime: PhantomData,
    };
    let p2 = ArgTy::Placeholder {
        value: NonNull::from(&y).cast::<()>(),
        formatter: show_u8,
        _lifetime: PhantomData,
    };
    let c = ArgTy::Count(513u16);
    println!("{}", eval(p1) as i64);
    println!("{}", eval(p2) as i64);
    println!("{}", eval(c) as i64);
    let arr = [p1, c, p2];
    let mut i = 0usize;
    let mut acc: u64 = 0;
    while i < 3 {
        acc = acc.wrapping_mul(31).wrapping_add(eval(arr[i]));
        i += 1;
    }
    println!("{}", acc as i64);
}
