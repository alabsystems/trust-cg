unsafe extern "Rust" {
 fn virtual_box(op:&Box<dyn Fn(&str,u64)->u64>, text:&str, seed:u64)->u64;
 fn virtual_box_mut(op:&mut Box<dyn FnMut(&mut[u64],u64)->u64>, data:&mut[u64], seed:u64)->u64;
}
fn main() {
 let op:Box<dyn Fn(&str,u64)->u64>=Box::new(|s,v| v+s.len() as u64+s.as_bytes().first().copied().unwrap_or(0) as u64);
 let mut hits=0;
 let mut op_mut:Box<dyn FnMut(&mut[u64],u64)->u64>=Box::new(move |s,v| {hits+=1;s[0]=v;hits+s.len() as u64});
 for i in 0..128u64 {
  let seed=i*0x9e3779b9;
  let text=if i%2==0 {"box"} else {""};
  assert_eq!(unsafe{virtual_box(&op,text,seed)},seed+text.len() as u64+text.as_bytes().first().copied().unwrap_or(0) as u64);
  let mut data=[0;3];
  assert_eq!(unsafe{virtual_box_mut(&mut op_mut,&mut data,seed)},i+4);
  assert_eq!(data[0],seed);
 }
 println!("PASS fat_fn_box checks=384");
}
