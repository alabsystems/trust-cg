use std::sync::atomic::{AtomicU64,Ordering};
static EVENTS:AtomicU64=AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn fat_event(v:u64){EVENTS.fetch_add(v,Ordering::Relaxed);}
unsafe extern "Rust" {
 fn virtual_all_const(op:&dyn Fn(&str,u64,bool)->u64)->u64;
 fn virtual_all_cstr(op:&dyn Fn(&core::ffi::CStr,u64,bool)->u64)->u64;
}
fn main(){
 let s=|x:&str,v:u64,f:bool|{assert!(!f);assert_eq!(x,"literal");v+x.len() as u64};
 let c=|x:&core::ffi::CStr,v:u64,f:bool|{assert!(!f);assert_eq!(x,c"abc");v+x.to_bytes_with_nul().len() as u64};
 assert_eq!(unsafe{virtual_all_const(&s)},98);
 assert_eq!(unsafe{virtual_all_cstr(&c)},75);
 assert_eq!(EVENTS.load(Ordering::Relaxed),2);
 println!("PASS fat_fn_constants checks=7");
}
