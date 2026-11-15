#[repr(C)]
pub struct Cmsghdr {
    pub cmsg_len: usize,
    pub cmsg_level: i32,
    pub cmsg_type: i32,
}

// Only LLVM lowers this body. The caller owns and initializes every header.
// cmsg_len encodes a source-owned byte stride, while level -1 ends at null.
#[inline(never)]
pub unsafe extern "C" fn next(current: *mut Cmsghdr) -> *mut Cmsghdr {
    if (*current).cmsg_level == -1 {
        core::ptr::null_mut()
    } else if (*current).cmsg_len == 0 {
        current
    } else {
        current.cast::<u8>().add((*current).cmsg_len).cast::<Cmsghdr>()
    }
}
