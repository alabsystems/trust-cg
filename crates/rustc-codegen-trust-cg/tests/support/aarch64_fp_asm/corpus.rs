#![no_std]
#![allow(unused_variables)]
use core::arch::asm;
#[unsafe(no_mangle)]
pub extern "C" fn fp32_fmadd(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        asm!("fmadd {x:s}, {x:s}, {y:s}, {z:s}", x=inout(vreg)x, y=in(vreg)y, z=in(vreg)z, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_fmadd_out(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        let out;
        asm!("fmadd {out:s}, {x:s}, {y:s}, {z:s}", out=lateout(vreg)out, z=in(vreg)z, x=in(vreg)x, y=in(vreg)y, options(pure,nomem,nostack,preserves_flags));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_alias(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        asm!("fmadd {x:s}, {y:s}, {x:s}, {x:s}", y=in(vreg)y, x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_sqrt(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        asm!("fsqrt {x:s}, {x:s}", x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_sqrt_out(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        let out;
        asm!("fsqrt {out:s}, {x:s}", out=out(vreg)out, x=in(vreg)x, options(pure,nomem,nostack));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_round(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        asm!("frintn {x:s}, {x:s}", x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_round_out(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        let out;
        asm!("frintn {out:s}, {x:s}", x=in(vreg)x, out=lateout(vreg)out, options(pure,nomem,nostack));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_loop(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        let mut i = 0;
        while i < n {
            asm!("fmadd {x:s}, {x:s}, {y:s}, {z:s}", x=inout(vreg)x, y=in(vreg)y, z=in(vreg)z, options(pure,nomem,nostack));
            i = i.wrapping_add(1);
        }
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp32_constant(mut x: f32, y: f32, z: f32, n: u32) -> f32 {
    unsafe {
        let a = 1.00000011920928955078125f32;
        let b = 0.99999988079071044921875f32;
        let c = -1.0f32;
        asm!("fmadd {out:s}, {a:s}, {b:s}, {c:s}",out=out(vreg)x,a=in(vreg)a,b=in(vreg)b,c=in(vreg)c,options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_fmadd(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        asm!("fmadd {x:d}, {x:d}, {y:d}, {z:d}", x=inout(vreg)x, y=in(vreg)y, z=in(vreg)z, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_fmadd_out(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        let out;
        asm!("fmadd {out:d}, {x:d}, {y:d}, {z:d}", out=lateout(vreg)out, z=in(vreg)z, x=in(vreg)x, y=in(vreg)y, options(pure,nomem,nostack,preserves_flags));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_alias(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        asm!("fmadd {x:d}, {y:d}, {x:d}, {x:d}", y=in(vreg)y, x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_sqrt(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        asm!("fsqrt {x:d}, {x:d}", x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_sqrt_out(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        let out;
        asm!("fsqrt {out:d}, {x:d}", out=out(vreg)out, x=in(vreg)x, options(pure,nomem,nostack));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_round(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        asm!("frintn {x:d}, {x:d}", x=inout(vreg)x, options(pure,nomem,nostack));
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_round_out(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        let out;
        asm!("frintn {out:d}, {x:d}", x=in(vreg)x, out=lateout(vreg)out, options(pure,nomem,nostack));
        x = out;
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_loop(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        let mut i = 0;
        while i < n {
            asm!("fmadd {x:d}, {x:d}, {y:d}, {z:d}", x=inout(vreg)x, y=in(vreg)y, z=in(vreg)z, options(pure,nomem,nostack));
            i = i.wrapping_add(1);
        }
    }
    x
}
#[unsafe(no_mangle)]
pub extern "C" fn fp64_constant(mut x: f64, y: f64, z: f64, n: u32) -> f64 {
    unsafe {
        let a = 1.0000000000000002220446049250313080847263336181640625f64;
        let b = 0.9999999999999997779553950749686919152736663818359375f64;
        let c = -1.0f64;
        asm!("fmadd {out:d}, {a:d}, {b:d}, {c:d}",out=out(vreg)x,a=in(vreg)a,b=in(vreg)b,c=in(vreg)c,options(pure,nomem,nostack));
    }
    x
}
