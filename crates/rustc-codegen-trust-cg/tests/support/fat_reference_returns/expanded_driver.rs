use std::fmt::Debug;
unsafe extern "Rust" {
    fn pick_slice<'a, 'b>(flag: bool, a: &'a &'b [u64], b: &'a &'b [u64]) -> &'a &'b [u64];
    fn pick_text<'a, 'b>(flag: bool, a: &'a &'b str, b: &'a &'b str) -> &'a &'b str;
    fn pick_object<'a, 'b>(
        flag: bool,
        a: &'a &'b dyn Debug,
        b: &'a &'b dyn Debug,
    ) -> &'a &'b dyn Debug;
    fn pick_raw_slice<'a>(flag: bool, a: &'a *const [u64], b: &'a *const [u64])
    -> &'a *const [u64];
    fn pick_raw_text<'a>(flag: bool, a: &'a *const str, b: &'a *const str) -> &'a *const str;
    fn pick_raw_object<'a>(
        flag: bool,
        a: &'a *const dyn Debug,
        b: &'a *const dyn Debug,
    ) -> &'a *const dyn Debug;
    fn pick_object_mut<'a, 'b>(
        flag: bool,
        a: &'a mut &'b dyn Debug,
        b: &'a mut &'b dyn Debug,
    ) -> &'a mut &'b dyn Debug;
}
fn main() {
    let mut checks = 0;
    macro_rules! check {
        ($x:expr) => {{
            assert!($x);
            checks += 1;
        }};
    }
    for seed in 0..256u64 {
        let data = [
            seed,
            seed.wrapping_mul(0xdeadbeef),
            !seed,
            seed.rotate_left(17),
        ];
        let other = [
            seed ^ 0xfeedface,
            seed + 9,
            seed.rotate_right(7),
            0,
            u64::MAX,
        ];
        let left_slice = &data[..(seed as usize % 5)];
        let right_slice = &other[..(seed as usize % 6)];
        let left_text = ["", "é", "two", "four", "🦀"][seed as usize % 5];
        let right_text = ["different", "", "λx", "😀zero"][seed as usize % 4];
        let left_object: &dyn Debug = &data;
        let right_object: &dyn Debug = &right_text;
        let replacement: &dyn Debug = &seed;
        for flag in [false, true] {
            unsafe {
                let a = pick_slice(flag, &left_slice, &right_slice);
                let expected = if flag { &left_slice } else { &right_slice };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                check!(*a == *expected);
                let a = pick_text(flag, &left_text, &right_text);
                let expected = if flag { &left_text } else { &right_text };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                check!(*a == *expected);
                let a = pick_object(flag, &left_object, &right_object);
                let expected = if flag { &left_object } else { &right_object };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                check!(format!("{:?}", *a) == format!("{:?}", *expected));
                let (left, right) = (left_slice as *const [u64], right_slice as *const [u64]);
                let a = pick_raw_slice(flag, &left, &right);
                let expected = if flag { &left } else { &right };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                let (left, right) = (left_text as *const str, right_text as *const str);
                let a = pick_raw_text(flag, &left, &right);
                let expected = if flag { &left } else { &right };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                let (left, right) = (
                    left_object as *const dyn Debug,
                    right_object as *const dyn Debug,
                );
                let a = pick_raw_object(flag, &left, &right);
                let expected = if flag { &left } else { &right };
                check!(std::ptr::eq(a, expected));
                check!(std::ptr::eq(*a, *expected));
                let (mut left, mut right) = (left_object, right_object);
                let address = if flag {
                    &mut left as *mut &dyn Debug
                } else {
                    &mut right as *mut &dyn Debug
                };
                let chosen = pick_object_mut(flag, &mut left, &mut right);
                check!(std::ptr::eq(chosen, address));
                *chosen = replacement;
                check!(std::ptr::eq(
                    left,
                    if flag { replacement } else { left_object }
                ));
                check!(std::ptr::eq(
                    right,
                    if flag { right_object } else { replacement }
                ));
            }
        }
    }
    assert_eq!(checks, 9216);
    println!("PASS trait_fat_reference_expanded checks={checks}");
}
