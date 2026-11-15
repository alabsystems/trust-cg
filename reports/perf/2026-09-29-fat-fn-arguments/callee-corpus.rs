#![no_std]
unsafe extern "Rust" {
 fn invoke_dynamic(op:&dyn Fn(u64,u64,u64,u64,u64,u64,&[u64],u64)->u64, data:&[u64], seed:u64)->u64;
}
#[unsafe(no_mangle)]
pub fn cg_fat_closure(data:&[u64],seed:u64)->u64 {
 let closure=|a,b,c,d,e,f,s:&[u64],g| a+b+c+d+e+f+g+s.len() as u64+s[0];
 unsafe {invoke_dynamic(&closure,data,seed)}
}
