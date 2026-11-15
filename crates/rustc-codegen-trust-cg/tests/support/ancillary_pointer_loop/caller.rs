extern crate ancillary_pointer_provider as provider;
extern crate ancillary_pointer_callee as callee;
use provider::Cmsghdr;

fn main() {
    assert_eq!(core::mem::size_of::<Cmsghdr>(), 16);
    assert_eq!(core::mem::align_of::<Cmsghdr>(), 8);
    assert_eq!(core::mem::offset_of!(Cmsghdr, cmsg_len), 0);
    assert_eq!(core::mem::offset_of!(Cmsghdr, cmsg_level), 8);
    assert_eq!(core::mem::offset_of!(Cmsghdr, cmsg_type), 12);
    let mut checks = 0;
    unsafe {
        assert!(callee::walk(core::ptr::null_mut()).is_null()); checks += 1;
        for count in 1..=9 {
            for null_end in [false, true] {
                let mut headers: Vec<Cmsghdr> = (0..count).map(|i| Cmsghdr {
                    cmsg_len: 16,
                    cmsg_level: 200 + i as i32,
                    cmsg_type: 1000 + i as i32,
                }).collect();
                let expected = headers.as_mut_ptr().add(count - 1);
                if null_end { (*expected).cmsg_level = -1; }
                else { (*expected).cmsg_len = 0; }
                let before: Vec<_> = headers.iter().map(|h| (h.cmsg_len, h.cmsg_level, h.cmsg_type)).collect();
                let actual = callee::walk(headers.as_mut_ptr());
                assert_eq!(actual, expected); checks += 1;
                assert_eq!((*actual).cmsg_type, 1000 + count as i32 - 1); checks += 1;
                assert_eq!((*actual).cmsg_level, if null_end { -1 } else { 200 + count as i32 - 1 }); checks += 1;
                assert_eq!(headers.iter().map(|h| (h.cmsg_len, h.cmsg_level, h.cmsg_type)).collect::<Vec<_>>(), before); checks += 1;
            }
        }
    }
    assert_eq!(checks, 73);
    println!("ANCILLARY_POINTER_NEXT|checks=73|layouts=5");
}
