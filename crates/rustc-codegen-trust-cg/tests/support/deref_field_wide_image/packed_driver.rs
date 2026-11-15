use packed::*;
fn main() {
    let mut t = Pk { a: 3, inner: vec![1u8, 2].into_boxed_slice() };
    set_packed(&mut t, vec![9u8; 5].into_boxed_slice());
    let inner = unsafe { std::ptr::read_unaligned(&raw const t.inner) };
    println!("packed a {} len {} sum {}", { t.a }, inner.len(), inner.iter().map(|&b| b as u32).sum::<u32>());
    std::mem::forget(inner);
}
