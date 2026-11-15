#[repr(transparent)]
struct Bytes([u8]);
unsafe extern "Rust" {
 fn tail_wrapped(bytes:&Bytes)->u8;
 fn trim_wrapped(bytes:&Bytes)->usize;
}
fn main() {
 let mut checks=0;
 for text in ["", "/", "//", "abc", "abc/", "abc//", "abc/d", "abc/d///"] {
  let bytes=unsafe {&*(text.as_bytes() as *const[u8] as *const Bytes)};
  assert_eq!(unsafe{tail_wrapped(bytes)},text.as_bytes().last().copied().unwrap_or(0));checks+=1;
  assert_eq!(unsafe{trim_wrapped(bytes)},text.trim_end_matches('/').len());checks+=1;
 }
 println!("PASS slice_from_end_wrapped checks={checks}");
}
