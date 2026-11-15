#![no_std]
#![feature(thread_local)]
#[repr(C, align(16))]
pub struct A16(pub [u64; 2]);
#[repr(C, align(16))]
pub struct R16 {
    pub first: &'static A16,
    pub second: &'static A16,
    pub rest: [u64; 0],
}
#[unsafe(no_mangle)]
pub static SA_RO_16: A16 = A16([4112; 2]);
#[unsafe(no_mangle)]
pub static mut SA_RW_16: A16 = A16([8208; 2]);
#[unsafe(no_mangle)]
pub static mut SA_ZERO_16: A16 = A16([0; 2]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TLS_16: A16 = A16([12304; 2]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TZ_16: A16 = A16([0; 2]);
#[unsafe(no_mangle)]
pub static SA_REL_16: R16 = R16 {
    first: &A16([16400; 2]),
    second: &A16([20496; 2]),
    rest: [24592; 0],
};
#[unsafe(no_mangle)]
pub static SA_MID_16: &u64 = &SA_RO_16.0[1];
#[unsafe(no_mangle)]
pub extern "C" fn sa_ro_16() -> *const u64 {
    (&raw const SA_RO_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rw_16() -> *mut u64 {
    (&raw mut SA_RW_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_zero_16() -> *mut u64 {
    (&raw mut SA_ZERO_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tls_16() -> *mut u64 {
    (&raw mut SA_TLS_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tz_16() -> *mut u64 {
    (&raw mut SA_TZ_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rel_16() -> *const u64 {
    (&raw const SA_REL_16).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_mid_16() -> *const u64 {
    (&raw const SA_MID_16).cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sa_write_16(zero: bool, i: usize, value: u64) -> u64 {
    let p = if zero {
        (&raw mut SA_ZERO_16).cast::<u64>()
    } else {
        (&raw mut SA_RW_16).cast::<u64>()
    };
    unsafe {
        p.add(i).write(value);
        p.add(i).read()
    }
}
#[repr(C, align(64))]
pub struct A64(pub [u64; 8]);
#[repr(C, align(64))]
pub struct R64 {
    pub first: &'static A64,
    pub second: &'static A64,
    pub rest: [u64; 6],
}
#[unsafe(no_mangle)]
pub static SA_RO_64: A64 = A64([4160; 8]);
#[unsafe(no_mangle)]
pub static mut SA_RW_64: A64 = A64([8256; 8]);
#[unsafe(no_mangle)]
pub static mut SA_ZERO_64: A64 = A64([0; 8]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TLS_64: A64 = A64([12352; 8]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TZ_64: A64 = A64([0; 8]);
#[unsafe(no_mangle)]
pub static SA_REL_64: R64 = R64 {
    first: &A64([16448; 8]),
    second: &A64([20544; 8]),
    rest: [24640; 6],
};
#[unsafe(no_mangle)]
pub static SA_MID_64: &u64 = &SA_RO_64.0[1];
#[unsafe(no_mangle)]
pub extern "C" fn sa_ro_64() -> *const u64 {
    (&raw const SA_RO_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rw_64() -> *mut u64 {
    (&raw mut SA_RW_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_zero_64() -> *mut u64 {
    (&raw mut SA_ZERO_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tls_64() -> *mut u64 {
    (&raw mut SA_TLS_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tz_64() -> *mut u64 {
    (&raw mut SA_TZ_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rel_64() -> *const u64 {
    (&raw const SA_REL_64).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_mid_64() -> *const u64 {
    (&raw const SA_MID_64).cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sa_write_64(zero: bool, i: usize, value: u64) -> u64 {
    let p = if zero {
        (&raw mut SA_ZERO_64).cast::<u64>()
    } else {
        (&raw mut SA_RW_64).cast::<u64>()
    };
    unsafe {
        p.add(i).write(value);
        p.add(i).read()
    }
}
#[repr(C, align(256))]
pub struct A256(pub [u64; 32]);
#[repr(C, align(256))]
pub struct R256 {
    pub first: &'static A256,
    pub second: &'static A256,
    pub rest: [u64; 30],
}
#[unsafe(no_mangle)]
pub static SA_RO_256: A256 = A256([4352; 32]);
#[unsafe(no_mangle)]
pub static mut SA_RW_256: A256 = A256([8448; 32]);
#[unsafe(no_mangle)]
pub static mut SA_ZERO_256: A256 = A256([0; 32]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TLS_256: A256 = A256([12544; 32]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TZ_256: A256 = A256([0; 32]);
#[unsafe(no_mangle)]
pub static SA_REL_256: R256 = R256 {
    first: &A256([16640; 32]),
    second: &A256([20736; 32]),
    rest: [24832; 30],
};
#[unsafe(no_mangle)]
pub static SA_MID_256: &u64 = &SA_RO_256.0[1];
#[unsafe(no_mangle)]
pub extern "C" fn sa_ro_256() -> *const u64 {
    (&raw const SA_RO_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rw_256() -> *mut u64 {
    (&raw mut SA_RW_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_zero_256() -> *mut u64 {
    (&raw mut SA_ZERO_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tls_256() -> *mut u64 {
    (&raw mut SA_TLS_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tz_256() -> *mut u64 {
    (&raw mut SA_TZ_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rel_256() -> *const u64 {
    (&raw const SA_REL_256).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_mid_256() -> *const u64 {
    (&raw const SA_MID_256).cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sa_write_256(zero: bool, i: usize, value: u64) -> u64 {
    let p = if zero {
        (&raw mut SA_ZERO_256).cast::<u64>()
    } else {
        (&raw mut SA_RW_256).cast::<u64>()
    };
    unsafe {
        p.add(i).write(value);
        p.add(i).read()
    }
}
#[repr(C, align(4096))]
pub struct A4096(pub [u64; 512]);
#[repr(C, align(4096))]
pub struct R4096 {
    pub first: &'static A4096,
    pub second: &'static A4096,
    pub rest: [u64; 510],
}
#[unsafe(no_mangle)]
pub static SA_RO_4096: A4096 = A4096([8192; 512]);
#[unsafe(no_mangle)]
pub static mut SA_RW_4096: A4096 = A4096([12288; 512]);
#[unsafe(no_mangle)]
pub static mut SA_ZERO_4096: A4096 = A4096([0; 512]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TLS_4096: A4096 = A4096([16384; 512]);
#[thread_local]
#[unsafe(no_mangle)]
pub static mut SA_TZ_4096: A4096 = A4096([0; 512]);
#[unsafe(no_mangle)]
pub static SA_REL_4096: R4096 = R4096 {
    first: &A4096([20480; 512]),
    second: &A4096([24576; 512]),
    rest: [28672; 510],
};
#[unsafe(no_mangle)]
pub static SA_MID_4096: &u64 = &SA_RO_4096.0[1];
#[unsafe(no_mangle)]
pub extern "C" fn sa_ro_4096() -> *const u64 {
    (&raw const SA_RO_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rw_4096() -> *mut u64 {
    (&raw mut SA_RW_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_zero_4096() -> *mut u64 {
    (&raw mut SA_ZERO_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tls_4096() -> *mut u64 {
    (&raw mut SA_TLS_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_tz_4096() -> *mut u64 {
    (&raw mut SA_TZ_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_rel_4096() -> *const u64 {
    (&raw const SA_REL_4096).cast()
}
#[unsafe(no_mangle)]
pub extern "C" fn sa_mid_4096() -> *const u64 {
    (&raw const SA_MID_4096).cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sa_write_4096(zero: bool, i: usize, value: u64) -> u64 {
    let p = if zero {
        (&raw mut SA_ZERO_4096).cast::<u64>()
    } else {
        (&raw mut SA_RW_4096).cast::<u64>()
    };
    unsafe {
        p.add(i).write(value);
        p.add(i).read()
    }
}
