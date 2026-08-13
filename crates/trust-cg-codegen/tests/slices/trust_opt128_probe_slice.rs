// Minimal Option<i128> 16-byte-tag probe: read an Option<i128>, and return an
// Option<i128> — exercises ONLY the 16-byte-tag READ + CONSTRUCT (no external
// leaves, no checked arithmetic). `incr1(k)`: None -> None ; Some(v) -> Some(v|1).
#![allow(dead_code)]

fn incr1(k: Option<i128>) -> Option<i128> {
    match k {
        Some(v) => Some(v | 1),
        None => None,
    }
}

#[no_mangle]
pub extern "C" fn incr1_entry(present: u32, hi: i64, lo: u64, which: u32) -> u64 {
    let k: Option<i128> = if present != 0 {
        Some(((hi as i128) << 64) | (lo as i128))
    } else {
        None
    };
    let r = incr1(k);
    match which {
        0 => match r { Some(_) => 1, None => 0 },
        1 => match r { Some(v) => v as u64, None => 0 },
        _ => match r { Some(v) => (v >> 64) as u64, None => 0 },
    }
}

fn main() {
    println!("{}", incr1_entry(1, 0, 4, 1)); // Some(4|1)=5
    println!("{}", incr1_entry(0, 0, 0, 0)); // None -> 0
}
