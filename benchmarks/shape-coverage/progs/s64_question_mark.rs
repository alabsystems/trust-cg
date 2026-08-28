// the ? operator on Result and Option (error/none propagation), unwrap_or.
use std::hint::black_box as bb;
fn parse(x: u64) -> Result<u64, u32> { if x % 7 == 0 { Err(x as u32 & 0xff) } else { Ok(x.wrapping_mul(2)) } }
fn chain(x: u64) -> Result<u64, u32> {
    let a = parse(x)?;
    let b = parse(a.wrapping_add(1))?;
    Ok(a.wrapping_add(b))
}
fn opt_chain(x: u64) -> Option<u64> {
    let a = if x > 3 { Some(x) } else { None }?;
    let b = if a < 100 { Some(a.wrapping_mul(3)) } else { None }?;
    Some(a.wrapping_add(b))
}
fn main() {
    let mut acc = 0u64;
    for i in 0..bb(40u64) {
        acc = acc.wrapping_add(chain(i).unwrap_or(0));
        acc = acc.wrapping_add(opt_chain(i).unwrap_or(0));
    }
    std::process::exit((acc % 233) as i32);
}
