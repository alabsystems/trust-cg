use std::{fmt::Debug, marker::PhantomData, ptr::NonNull};
#[repr(C)]
pub struct Cursor<'a> {
    pub ptr: NonNull<&'a dyn Debug>,
    pub end_or_len: *const &'a dyn Debug,
    pub marker: PhantomData<&'a &'a dyn Debug>,
}
impl<'a> Cursor<'a> {
    fn new(values: &'a [&'a dyn Debug]) -> Self {
        Self {
            ptr: NonNull::new(values.as_ptr() as *mut &'a dyn Debug).unwrap(),
            end_or_len: unsafe { values.as_ptr().add(values.len()) },
            marker: PhantomData,
        }
    }
    fn len(&self) -> usize {
        (self.end_or_len as usize - self.ptr.as_ptr() as usize) / std::mem::size_of::<&dyn Debug>()
    }
}
unsafe extern "Rust" {
    fn next_debug<'a>(it: &mut Cursor<'a>) -> Option<&'a &'a dyn Debug>;
}
fn main() {
    let mut checks = 0;
    for i in 0..256u64 {
        let signed = -(i as i64);
        let wide = (i as u128) << 71;
        let byte = i as u8;
        let boolean = i % 2 == 0;
        let character = char::from_u32(0x1f600 + (i % 64) as u32).unwrap();
        let number = i as f64 + 0.5;
        let text = "borrowed trait value";
        let empty = ();
        let values: [&dyn Debug; 8] = [
            &signed, &wide, &byte, &boolean, &character, &number, &text, &empty,
        ];
        for len in 0..=8 {
            let mut it = Cursor::new(&values[..len]);
            assert_eq!(it.len(), len);
            checks += 1;
            for j in 0..len + 2 {
                let got = unsafe { next_debug(&mut it) };
                if j < len {
                    let value = got.expect("missing item");
                    assert!(std::ptr::eq(value, &values[j]));
                    checks += 1;
                    assert!(std::ptr::eq::<dyn Debug>(*value, values[j]));
                    checks += 1;
                    assert_eq!(format!("{value:?}"), format!("{:?}", values[j]));
                    checks += 1;
                } else {
                    assert!(got.is_none());
                    checks += 1;
                }
                assert_eq!(it.len(), len.saturating_sub(j + 1));
                checks += 1;
            }
        }
    }
    println!("PASS trait_iterator_cursor checks={checks}");
}
