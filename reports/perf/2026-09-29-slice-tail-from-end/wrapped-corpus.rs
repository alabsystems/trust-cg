#![no_std]
#[repr(transparent)]
pub struct Bytes([u8]);
#[unsafe(no_mangle)]
pub fn tail_wrapped(bytes: &Bytes) -> u8 {
    match &bytes.0 { [.., last] => *last, _ => 0 }
}
#[unsafe(no_mangle)]
pub fn trim_wrapped(bytes: &Bytes) -> usize {
    let mut data=&bytes.0;
    while let Some((last,init))=data.split_last() && *last==b'/' {data=init;}
    data.len()
}
