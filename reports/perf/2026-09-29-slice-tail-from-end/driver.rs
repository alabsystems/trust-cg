unsafe extern "Rust" {
 fn tail_word(words:&[u64])->u64;
 fn end_words(words:&[u64])->u64;
 fn tail_mut(words:&mut[u64],mask:u64)->u64;
}
fn main() {
 let mut checks=0;
 for len in 0..128usize {
  let mut words:Vec<u64>=(0..len).map(|n| (n as u64).wrapping_mul(0x9e3779b97f4a7c15)).collect();
  assert_eq!(unsafe{tail_word(&words)},words.last().copied().unwrap_or(0));checks+=1;
  assert_eq!(unsafe{end_words(&words)},if len>=2{words[0]^words[len-1]}else{0});checks+=1;
  let mut expected=words.clone();if let Some(x)=expected.last_mut(){*x^=0xa5a5a5a5a5a5a5a5;}
  assert_eq!(unsafe{tail_mut(&mut words,0xa5a5a5a5a5a5a5a5)},expected.last().copied().unwrap_or(0));checks+=1;
  assert_eq!(words,expected);checks+=1;
 }
 println!("PASS slice_from_end checks={checks}");
}
