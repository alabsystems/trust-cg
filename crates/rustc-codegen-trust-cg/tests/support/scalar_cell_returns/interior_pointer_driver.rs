unsafe extern "Rust" {
    fn alias_pointer(before: *mut u8, after: *mut u8) -> *mut u8;
}

fn main() {
    let mut left = [0x11u8; 64];
    let mut right = [0x7cu8; 64];
    let mut checks = 0;
    for round in 0..32 {
        for index in 0..64 {
            let after_index = (17 * index + round) % 64;
            let before = unsafe { left.as_mut_ptr().add(index) };
            let after = unsafe { right.as_mut_ptr().add(after_index) };
            let left_before = left;
            let right_before = right;
            let returned = unsafe { alias_pointer(before, after) };
            assert_eq!(returned, after);
            assert_eq!(unsafe { alias_pointer(after, before) }, before);
            assert_eq!(left, left_before);
            assert_eq!(right, right_before);

            let written = (round as u8).wrapping_mul(19).wrapping_add(index as u8);
            unsafe { returned.write(written) };
            let mut expected = right_before;
            expected[after_index] = written;
            assert_eq!(right, expected);
            assert_eq!(left, left_before);
            assert_eq!(
                unsafe { alias_pointer(before, core::ptr::null_mut()) },
                core::ptr::null_mut()
            );
            assert_eq!(
                unsafe { alias_pointer(core::ptr::null_mut(), after) },
                after
            );
            checks += 8;
        }
    }
    assert_eq!(checks, 16384);
    println!("PASS scalar_cell_return_interior_pointer checks={checks}");
}
