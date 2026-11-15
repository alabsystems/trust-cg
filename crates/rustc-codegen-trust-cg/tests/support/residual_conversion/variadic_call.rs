unsafe extern "C" {
    fn variadic_words(count: u32, ...) -> u64;
    fn variadic_mixed(tag: u64, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_words(a: u64, b: u64) -> u64 {
    unsafe { variadic_words(2, a, b) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_empty() -> u64 {
    unsafe { variadic_words(0) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_mixed(a: i32, b: f64, ptr: *const u64) -> u64 {
    unsafe { variadic_mixed(17, a, b, ptr) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_spill(a: u64) -> u64 {
    unsafe {
        variadic_words(
            10,
            a,
            a.wrapping_add(1),
            a.wrapping_add(2),
            a.wrapping_add(3),
            a.wrapping_add(4),
            a.wrapping_add(5),
            a.wrapping_add(6),
            a.wrapping_add(7),
            a.wrapping_add(8),
            a.wrapping_add(9),
        )
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_pointer_empty(f: unsafe extern "C" fn(u32, ...) -> u64) -> u64 {
    unsafe { f(0) }
}

unsafe extern "C" {
    fn variadic_floats(count: u32, ...) -> f64;
    fn variadic_cross(count: u32, ...) -> u64;
    fn variadic_fixed(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        count: u32,
        ...
    ) -> u64;
    fn variadic_fixed_float(a: f32, b: f64, count: u32, ...) -> f64;
    fn variadic_promoted(tag: u32, ...) -> u64;
    fn syscall(number: isize, ...) -> isize;
    fn getpid() -> i32;
    fn open(path: *const u8, flags: i32, ...) -> i32;
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
    fn close(fd: i32) -> i32;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_floats(d: f64) -> f64 {
    unsafe {
        variadic_floats(
            10,
            d,
            d + 1.0,
            d + 2.0,
            d + 3.0,
            d + 4.0,
            d + 5.0,
            d + 6.0,
            d + 7.0,
            d + 8.0,
            d + 9.0,
        )
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_cross(a: u64, d: f64) -> u64 {
    unsafe {
        variadic_cross(
            10,
            a,
            d,
            a.wrapping_add(1),
            d + 1.0,
            a.wrapping_add(2),
            d + 2.0,
            a.wrapping_add(3),
            d + 3.0,
            a.wrapping_add(4),
            d + 4.0,
            a.wrapping_add(5),
            d + 5.0,
            a.wrapping_add(6),
            d + 6.0,
            a.wrapping_add(7),
            d + 7.0,
            a.wrapping_add(8),
            d + 8.0,
            a.wrapping_add(9),
            d + 9.0,
            -17i32,
        )
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_fixed(a: u64, b: u64) -> u64 {
    unsafe {
        variadic_fixed(
            a,
            b,
            a ^ b,
            !a,
            !b,
            a.wrapping_add(b),
            a.wrapping_sub(b),
            3,
            b,
            a,
            a ^ 17,
        )
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_fixed_float(a: f32, b: f64) -> f64 {
    unsafe {
        variadic_fixed_float(
            a,
            b,
            8,
            b + 1.0,
            b + 2.0,
            b + 3.0,
            b + 4.0,
            b + 5.0,
            b + 6.0,
            b + 7.0,
            b + 8.0,
        )
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_promoted(
    a: i32,
    b: u32,
    c: i64,
    d: u64,
    e: isize,
    f: usize,
    p: *const u64,
) -> u64 {
    unsafe { variadic_promoted(19, a, b, c, d, e, f, p) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_libc() -> bool {
    // Linux AArch64 __NR_getpid = 172. No anonymous arguments here.
    if unsafe { syscall(172) } != unsafe { getpid() } as isize {
        return false;
    }
    let fd = unsafe { open(c"/dev/null".as_ptr().cast(), 0, 0u32) };
    if fd < 0 {
        return false;
    }
    // F_SETFD = 2, FD_CLOEXEC = 1, F_GETFD = 1; one- and zero-extra calls.
    let mut byte = 0x5au8;
    // __NR_read = 63; /dev/null returns EOF without changing the buffer.
    let read = unsafe { syscall(63, fd, &raw mut byte, 1usize) };
    let set = unsafe { fcntl(fd, 2, 1i32) };
    let got = unsafe { fcntl(fd, 1) };
    let closed = unsafe { close(fd) };
    read == 0 && byte == 0x5a && set == 0 && got == 1 && closed == 0
}
