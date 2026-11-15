#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

static mut LOG: u64 = 0;
static mut DROPS: u32 = 0;

#[inline(never)]
fn log(v: u32) {
    unsafe {
        LOG = LOG.wrapping_mul(31).wrapping_add(v as u64);
        DROPS += 1;
    }
}

#[inline(never)]
fn reset() {
    unsafe {
        LOG = 7;
        DROPS = 0;
    }
}

#[inline(never)]
fn result() -> u64 {
    unsafe { LOG ^ (DROPS as u64) << 48 }
}

struct Guard {
    id: u32,
}
impl Drop for Guard {
    fn drop(&mut self) {
        log(self.id);
    }
}

struct Pair2 {
    a: Guard,
    b: Guard,
    x: u32,
}

#[inline(never)]
fn scoped(n: u32) -> u32 {
    let _g1 = Guard { id: 1 };
    let mut acc = 0;
    for i in 0..(n % 6) {
        let g = Guard { id: 10 + i };
        if i == 3 {
            return acc + g.id;
        }
        acc += g.id;
    }
    let _g2 = Guard { id: 2 };
    acc
}

#[inline(never)]
fn consume(g: Guard) -> u32 {
    g.id * 2
}

#[inline(never)]
fn cond_move(flag: u32) -> u32 {
    let g = Guard { id: 100 };
    let h = Guard { id: 200 };
    let mut r = 0;
    if flag & 1 == 1 {
        r += consume(g);
    }
    if flag & 2 == 2 {
        let keep = h;
        r += keep.id;
    }
    log(999);
    r
}

#[inline(never)]
fn struct_fields(k: u32) -> u32 {
    let p = Pair2 {
        a: Guard { id: 30 + k },
        b: Guard { id: 40 },
        x: k,
    };
    let Pair2 { a, b: _, x } = p;
    let r = a.id + x;
    drop(a);
    log(5);
    r
}

#[inline(never)]
fn opt_take(k: u32) -> u32 {
    let mut slot: Option<Guard> = if k % 3 == 0 {
        None
    } else {
        Some(Guard { id: 50 + k % 7 })
    };
    let taken = slot.take();
    let r = match &taken {
        Some(g) => g.id,
        None => 0,
    };
    let old = core::mem::replace(&mut slot, Some(Guard { id: 60 }));
    let r2 = old.is_some() as u32;
    if k & 4 == 4 {
        slot = None;
        log(7);
    }
    r * 10 + r2
}

#[inline(never)]
fn array_drop(k: u32) -> u32 {
    let arr = [Guard { id: 1 }, Guard { id: 2 }, Guard { id: 3 }];
    let mut s = 0;
    for g in arr.iter() {
        s += g.id * k;
    }
    s
}

#[inline(never)]
fn swap_guards(k: u32) -> u32 {
    let mut a = Guard { id: 70 };
    let mut b = Guard { id: 80 + k % 5 };
    if k & 1 == 1 {
        core::mem::swap(&mut a, &mut b);
    }
    let c = core::mem::replace(&mut a, Guard { id: 90 });
    let r = c.id * 1000 + a.id + b.id;
    drop(b);
    r
}

#[inline(never)]
fn loop_reassign(n: u32) -> u32 {
    let mut g = Guard { id: 0 };
    for i in 1..=(n % 8) {
        g = Guard { id: i * 11 };
    }
    let r = g.id;
    core::mem::forget(Guard { id: 12345 });
    r
}

#[inline(never)]
fn early_q(v: u32) -> Option<u32> {
    let _a = Guard { id: 300 };
    let x = if v % 2 == 0 { Some(v) } else { None }?;
    let _b = Guard { id: 301 };
    let y = if v % 3 == 0 { None } else { Some(x + 1) }?;
    Some(y * 2)
}

#[no_mangle]
pub extern "C" fn drop_cond_move(flag: u32) -> u64 {
    reset();
    let r = cond_move(flag);
    result() ^ (r as u64) << 32
}
