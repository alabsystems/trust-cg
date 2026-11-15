use std::sync::atomic::{AtomicU64, Ordering};
use std::ffi::CStr;
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn fat_event(value: u64) { EVENTS.store(EVENTS.load(Ordering::Relaxed)*10+value, Ordering::Relaxed); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { fat_event(2); } }
#[repr(C)]
struct Header { head: u64, tail: [u8] }
#[repr(C)]
struct HeaderImage { head: u64, tail: [u8;5] }
unsafe extern "Rust" {
    fn virtual_str(op: &dyn Fn(&str,u64,bool)->u64, text:&str, seed:u64, fail:bool)->u64;
    fn virtual_slice(op: &mut dyn FnMut(&mut [u64],u64,bool)->u64, data:&mut [u64], seed:u64, fail:bool)->u64;
    fn virtual_const(op: &dyn Fn(&str,u64,bool)->u64, seed:u64, fail:bool)->u64;
    fn virtual_cstr(op: &dyn Fn(&CStr,u64,bool)->u64, text:&CStr, seed:u64, fail:bool)->u64;
    fn virtual_raw(op: &dyn Fn(*const [u16],u64,bool)->u64, data:*const [u16], seed:u64, fail:bool)->u64;
    fn virtual_split(op: &dyn Fn(u64,u64,u64,u64,u64,u64,&[u64],u64,bool)->u64, data:&[u64], seed:u64, fail:bool)->u64;
    fn virtual_zst(op:&dyn Fn(u64,(),&str,bool)->u64, text:&str, seed:u64, fail:bool)->u64;
    fn virtual_mixed(op:&dyn Fn(f64,u8,&str,&[u16],bool)->u64, text:&str, data:&[u16], seed:u64, fail:bool)->u64;
    fn virtual_dst(op:&dyn Fn(&Header,u64,bool)->u64, data:&Header, seed:u64, fail:bool)->u64;
}
fn answer(seed:u64, fail:bool, value:u64)->u64 {
    let _guard=Guard;
    if fail { std::panic::panic_any(seed); }
    value
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let string=|s:&str,v:u64,f:bool| answer(v,f,v+s.len() as u64+s.as_bytes().first().copied().unwrap_or(0) as u64);
    let cstring=|s:&CStr,v:u64,f:bool| answer(v,f,v+s.to_bytes_with_nul().len() as u64+s.to_bytes().first().copied().unwrap_or(0) as u64);
    let raw=|p:*const[u16],v:u64,f:bool| { let a=unsafe{&*p};answer(v,f,v+a.len() as u64+a.first().copied().unwrap_or(0) as u64) };
    let split=|a,b,c,d,e,g,s:&[u64],h,f| { assert_eq!([b,c,d,e,g,h],[a+1,a+2,a+3,a+4,a+5,a+6]); answer(a,f,a*7+21+s.len() as u64+s.first().copied().unwrap_or(0)) };
    let zst=|v,(),s:&str,f| string(s,v,f);
    let mixed=|a:f64,b:u8,s:&str,t:&[u16],f| { let v=a as u64;assert_eq!(a,v as f64+0.25);assert_eq!(b,v as u8);answer(v,f,v+b as u64+s.len() as u64+t.len() as u64+t.first().copied().unwrap_or(0) as u64) };
    let dst=|h:&Header,v:u64,f| answer(v,f,v+h.head+h.tail.len() as u64+h.tail[4] as u64);
    let mut checks=0;let mut panics=0;
    for seed in 0..128u64 {
        let text=if seed%2==0 { "bonjour" } else { "" };
        let ctext=if seed%2==0 { c"bonjour" } else { c"" };
        let words=[91u16,17,42];let words=&words[..(seed%4) as usize];
        let split_words=[seed^77,seed^81];let split_words=&split_words[..(seed%3) as usize];
        let image=HeaderImage{head:seed^55,tail:[7,11,13,17,19]};
        let header=unsafe { &*(std::ptr::slice_from_raw_parts((&image as *const HeaderImage).cast::<u8>(),5) as *const Header) };
        for kind in 0..9 {
            for fail in [false,true] {
                if fail && cfg!(panic="abort") {continue;}
                EVENTS.store(0,Ordering::Relaxed);
                let mut hits=0;let mut data=[0u64;5];
                let mut slice=|s:&mut[u64],v:u64,f| {hits+=1;s[0]=v;answer(v,f,v+s.len() as u64)};
                let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                    match kind {
                        0=>virtual_str(&string,text,seed,fail),
                        1=>virtual_slice(&mut slice,&mut data,seed,fail),
                        2=>virtual_const(&string,seed,fail),
                        3=>virtual_cstr(&cstring,ctext,seed,fail),
                        4=>virtual_raw(&raw,words,seed,fail),
                        5=>virtual_split(&split,split_words,seed,fail),
                        6=>virtual_zst(&zst,text,seed,fail),
                        7=>virtual_mixed(&mixed,text,words,seed,fail),
                        _=>virtual_dst(&dst,header,seed,fail),
                    }
                }));
                if fail { assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(),seed);panics+=1; }
                else {
                    let expected=match kind {
                        0|6=>seed+text.len() as u64+text.as_bytes().first().copied().unwrap_or(0) as u64,
                        1=>seed+5,
                        2=>seed+5+104,
                        3=>seed+ctext.to_bytes_with_nul().len() as u64+ctext.to_bytes().first().copied().unwrap_or(0) as u64,
                        4=>seed+words.len() as u64+words.first().copied().unwrap_or(0) as u64,
                        5=>seed*7+21+split_words.len() as u64+split_words.first().copied().unwrap_or(0),
                        7=>seed+(seed as u8) as u64+text.len() as u64+words.len() as u64+words.first().copied().unwrap_or(0) as u64,
                        _=>seed+(seed^55)+5+19,
                    };
                    assert_eq!(result.unwrap(),expected);
                }
                assert_eq!(EVENTS.load(Ordering::Relaxed),21);checks+=2;
                if kind==1 {assert_eq!(data[0],seed);assert_eq!(hits,1);checks+=2;}
            }
        }
    }
    println!("PASS fat_fn_expanded checks={checks} panics={panics}");
}
