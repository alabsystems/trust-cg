// (h) An indirect call through a `fn(&str)` / `fn(&[T])` POINTER dropped the
// `len` half of the fat-pointer argument: `lower_indirect_call_terminator`
// hand-built its signature with `&str` as one `Ptr` while the shared arg lowering
// passed the `{ data, len }` slot (`3 12` expected, a stack address printed).
// Fixed: the indirect signature now comes from `classify_func_ty`, the same
// classifier every direct call and every callee body use.
fn slen(s: &str) -> usize { s.len() }
fn ssum(s: &[u8]) -> u32 { s.iter().map(|b| *b as u32).sum::<u32>() + s.len() as u32 * 100 }
fn main() {
    let a = slen("abcd");
    let p: fn(&str) -> usize = slen;
    let b = p("abc");
    let c = p("");
    let q: fn(&[u8]) -> u32 = ssum;
    let d = q(&[1, 2, 3]);
    let e = q(&[]);
    println!("{} {} {} {} {}", a, b, c, d, e);
}
