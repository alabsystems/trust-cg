#[unsafe(no_mangle)]
pub fn invoke_dynamic(op:&dyn Fn(u64,u64,u64,u64,u64,u64,&[u64],u64)->u64,data:&[u64],seed:u64)->u64 {
 op(seed,seed+1,seed+2,seed+3,seed+4,seed+5,data,seed+6)
}
unsafe extern "Rust" {fn cg_fat_closure(data:&[u64],seed:u64)->u64;}
fn main(){for seed in 0..128{assert_eq!(unsafe{cg_fat_closure(&[71,99],seed)},seed*7+21+2+71);}println!("PASS fat_fn_callee checks=128");}
