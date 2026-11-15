extern crate ancillary_pointer_provider as provider;
use provider::Cmsghdr;

// This is the source-shaped CMSG_NXTHDR loop: previous is updated before the
// opaque next-header call. Returned pointer identity is visible to LLVM.
#[inline(never)]
pub unsafe extern "C" fn walk(mut current: *mut Cmsghdr) -> *mut Cmsghdr {
    let mut previous = current;
    while !current.is_null() {
        previous = current;
        current = provider::next(current);
        if core::ptr::eq(current, previous) {
            break;
        }
    }
    previous
}
