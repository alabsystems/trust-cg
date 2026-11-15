#[repr(C)]
pub struct Triple {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[repr(C)]
pub struct Nested {
    pub first: u32,
    pub rest: [u32; 2],
}
pub struct Reordered {
    pub small: u8,
    pub big: u64,
    pub middle: u16,
}
unsafe extern "Rust" {
    fn choose_shared(value: &Triple, first: bool) -> &u32;
    fn choose_mut(value: &mut Triple, first: bool) -> &mut u32;
    fn call_first(value: &Triple, callback: fn(&u32) -> u32) -> u32;
    fn call_last(value: &mut Triple, callback: fn(&mut u32));
    fn first_nested(value: &Nested) -> &u32;
    fn first_nested_mut(value: &mut Nested) -> &mut u32;
    fn first_reordered(value: &Reordered) -> &u64;
    fn first_reborrow(value: &Triple) -> &u32;
    fn last_reborrow(value: &Triple) -> &u32;
    fn first_array(value: &[u32; 3]) -> &u32;
    fn last_array(value: &[u32; 3]) -> &u32;
    fn first_struct(value: &Triple) -> &u32;
    fn last_struct(value: &Triple) -> &u32;
    fn mutate_array(value: &mut [u32; 3]) -> &mut u32;
    fn mutate_struct(value: &mut Triple) -> &mut u32;
}
fn read(value: &u32) -> u32 {
    value.rotate_left(7) ^ 0x12345678
}
fn mutate(value: &mut u32) {
    *value = value.rotate_right(11) ^ 0x87654321;
}
fn main() {
    for seed in 0..4096_u32 {
        let mut a = [seed, seed ^ 0x55, seed.wrapping_mul(0x91234567)];
        let mut b = Triple {
            a: a[0],
            b: a[1],
            c: a[2],
        };
        let mut c = Nested {
            first: seed,
            rest: [seed + 1, seed + 2],
        };
        let d = Reordered {
            small: seed as u8,
            big: seed as u64,
            middle: seed as u16,
        };
        unsafe {
            assert_eq!(first_nested(&c) as *const u32, &c.first as *const u32);
            assert_eq!(first_reordered(&d) as *const u64, &d.big as *const u64);
            assert_eq!(first_reborrow(&b) as *const u32, &b.a as *const u32);
            assert_eq!(last_reborrow(&b) as *const u32, &b.c as *const u32);
            *first_nested_mut(&mut c) = 0xfedcba98;
            assert_eq!(first_array(&a) as *const u32, &a[0] as *const u32);
            assert_eq!(last_array(&a) as *const u32, &a[2] as *const u32);
            assert_eq!(first_struct(&b) as *const u32, &b.a as *const u32);
            assert_eq!(last_struct(&b) as *const u32, &b.c as *const u32);
            *mutate_array(&mut a) = 0x12345678;
            *mutate_struct(&mut b) = 0x98765432;
        }
        assert_eq!(c.first, 0xfedcba98);
        assert_eq!(a[0], 0x12345678);
        assert_eq!(b.c, 0x98765432);
        for first in [false, true] {
            let expected = if first {
                &b.a as *const u32
            } else {
                &b.c as *const u32
            };
            assert_eq!(unsafe { choose_shared(&b, first) } as *const u32, expected);
            let expected = if first { &raw mut b.a } else { &raw mut b.c };
            let selected = unsafe { choose_mut(&mut b, first) };
            assert_eq!(selected as *mut u32, expected);
            *selected = seed ^ 0xf00d1234;
            assert_eq!(if first { b.a } else { b.c }, seed ^ 0xf00d1234);
        }
        assert_eq!(
            unsafe { call_first(&b, std::hint::black_box(read)) },
            read(&b.a)
        );
        let mut expected = b.c;
        mutate(&mut expected);
        unsafe {
            call_last(&mut b, std::hint::black_box(mutate));
        }
        assert_eq!(b.c, expected);
    }
    println!("PASS projected_reference_types checks=77824");
}
