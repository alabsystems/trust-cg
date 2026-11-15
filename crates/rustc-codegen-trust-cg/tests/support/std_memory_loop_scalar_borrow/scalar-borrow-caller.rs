extern crate scalar_borrow_library;

unsafe extern "C" {
    fn scalar_payload_guard(code: i32, present: bool, guard: bool) -> i32;
}

fn main() {
    assert_eq!(std::mem::size_of::<Option<i32>>(), 8);
    assert_eq!(std::mem::align_of::<Option<i32>>(), 4);
    let mut checks = 0;
    for code in [-20, 0, 3, 7, 11, 19, 23, 30] {
        for present in [false, true] {
            for guard in [false, true] {
                let expected = if !present { -3000 }
                    else if guard && [3, 7, 11, 19, 23].contains(&code) { code + 1000 }
                    else { code - 1000 };
                let actual = unsafe { scalar_payload_guard(code, present, guard) };
                assert_eq!(actual, expected, "code={code} present={present} guard={guard}");
                checks += 1;
            }
        }
    }
    assert_eq!(checks, 32);
    println!("PROJECTED_SCALAR_PAYLOAD_GUARD_NATIVE checks=32 layouts=2");
}
