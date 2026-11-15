unsafe extern "C" {fn unit_call(seed:u64)->u64;fn flow_map(seed:u64)->u64;}
fn main(){for seed in 0..4096 {unsafe{assert_eq!(unit_call(seed),seed+17);assert_eq!(flow_map(seed),seed+if seed&1==0 {7}else{11});}}println!("PASS zst_tuple checks=8192");}
