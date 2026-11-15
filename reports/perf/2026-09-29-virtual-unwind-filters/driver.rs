use std::sync::atomic::{AtomicU64,Ordering};
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn virtual_event(code:u64) { let old=EVENTS.load(Ordering::Relaxed);EVENTS.store(old*10+code,Ordering::Relaxed); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { virtual_event(2); } }
trait Operation { fn run(&mut self, value:u64, fail:bool)->u64; }
#[repr(C)]
struct Pair { a:u64, b:u64 }
trait PairOperation { fn run(&mut self, value:u64, fail:bool)->Pair; }
struct Method;
impl Operation for Method {fn run(&mut self,value:u64,fail:bool)->u64 {let _guard=Guard;if fail{std::panic::panic_any(value);}value.wrapping_add(13)}}
impl PairOperation for Method {fn run(&mut self,value:u64,fail:bool)->Pair {let _guard=Guard;if fail{std::panic::panic_any(value);}Pair{a:value.wrapping_add(13),b:!value}}}
unsafe extern "Rust" {
    fn virtual_scalar(op:&mut dyn Operation,value:u64,fail:bool)->u64;
    fn virtual_pair(op:&mut dyn PairOperation,value:u64,fail:bool)->u64;
    fn virtual_fn(op:&dyn Fn(u64,bool)->u64,value:u64,fail:bool)->u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let closure=|value:u64,fail:bool| {let _guard=Guard;if fail{std::panic::panic_any(value);}value.wrapping_add(13)};
    for index in 0..128u64 {let value=index.wrapping_mul(0x9e3779b97f4a7c15);for kind in 0..3 {for fail in [false,true] {
        EVENTS.store(0,Ordering::Relaxed);
        let mut method=Method;
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||unsafe {match kind{0=>virtual_scalar(&mut method,value,fail),1=>virtual_pair(&mut method,value,fail),_=>virtual_fn(&closure,value,fail)}}));
        if fail {assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(),value);} else {assert_eq!(result.unwrap(),if kind==1{value.wrapping_add(13)^!value}else{value.wrapping_add(13)});}
        assert_eq!(EVENTS.load(Ordering::Relaxed),21);
    }}}
    println!("PASS virtual_unwind checks=1536 panics=384");
}
