// CORPUS FIXTURE — lane types-slices-str-arrays #1: fat-reference RETURNS and
// SUBSLICE reborrows.
//   * a callee returning `&[u8]` / `&str` (`tail`/`head`/`mid`/`str_tail`) used to
//     be refused by the promoted-scalar-ref-return CLASSIFIER on the pointee's own
//     `Ty::[u8]` / `Ty::str` mapping; it now declines and the call flows through
//     the `{ data, len }` slot return path;
//   * `[first, rest @ ..]` / `[head @ .., last]` / `[_, mid @ .., _]` slice-pattern
//     bindings lower a `ProjectionElem::Subslice` reborrow: `data + from*size`,
//     `len - from - to` (a `u16` element proves the stride).
// Every placeholder is a plain integer local and lengths pass through `keep` (an
// opaque call): the fmt interception refuses a `.len()` / runtime `&str`
// placeholder ITSELF, which is not what this fixture measures. Every printed value
// depends on a data pointer or a length the lowered shapes compute, so the
// bridge-vs-LLVM output must be byte-identical.
#[inline(never)]
fn keep(x: usize) -> u64 { x as u64 }
#[inline(never)]
fn tail(s: &[u8]) -> &[u8] { &s[1..] }
#[inline(never)]
fn head(s: &[u8], n: usize) -> &[u8] { &s[..n] }
#[inline(never)]
fn mid(s: &[u8], a: usize, b: usize) -> &[u8] { &s[a..b] }
#[inline(never)]
fn str_tail(s: &str) -> &str { &s[1..] }
#[inline(never)]
fn total(s: &[u8]) -> u64 {
    let (mut t, mut i) = (0u64, 0);
    while i < s.len() { t = t * 10 + s[i] as u64; i += 1; }
    t
}
#[inline(never)]
fn split_first(s: &[u8]) -> Option<(&u8, &[u8])> {
    if let [first, tail @ ..] = s { Some((first, tail)) } else { None }
}
#[inline(never)]
fn strip_sign(src: &[u8]) -> (bool, &[u8]) {
    match src {
        [b'+' | b'-'] => (true, src),
        [b'+', rest @ ..] => (true, rest),
        [b'-', rest @ ..] => (false, rest),
        _ => (true, src),
    }
}
#[inline(never)]
fn drop_last(s: &[u8]) -> &[u8] { if let [head @ .., _last] = s { head } else { s } }
#[inline(never)]
fn middle(s: &[u16]) -> &[u16] { if let [_a, mid @ .., _z] = s { mid } else { s } }
fn main() {
    let data: [u8; 6] = [1, 2, 3, 4, 5, 6];
    let s: &[u8] = &data;
    let (a, b, c) = (total(tail(s)), total(head(s, 3)), total(mid(s, 2, 5)));
    let n = keep(s.len());
    println!("{} {} {} {}", a, b, c, n);
    let t = str_tail("hello");
    let (tn, t0, t3) = (keep(t.len()), t.as_bytes()[0], t.as_bytes()[3]);
    println!("{} {} {}", tn, t0, t3);
    let d = [b'-', b'1', b'2'];
    let (pos, rest) = strip_sign(&d);
    let (p, rn, r0) = (pos as u8, keep(rest.len()), rest[0]);
    println!("{} {} {}", p, rn, r0);
    let (pos2, rest2) = strip_sign(&[b'+']);
    let (p2, rn2) = (pos2 as u8, keep(rest2.len()));
    println!("{} {}", p2, rn2);
    let (f, sf) = split_first(&d).map(|(f, t)| (*f, keep(t.len()) * 100 + t[1] as u64)).unwrap_or((0, 0));
    println!("{} {}", f, sf);
    let dl = drop_last(&data);
    let (dn, dt) = (keep(dl.len()), total(dl));
    println!("{} {}", dn, dt);
    let w: [u16; 5] = [10, 20, 30, 40, 50];
    let m = middle(&w);
    let (mn, m0, m2) = (keep(m.len()), m[0], m[2]);
    println!("{} {} {}", mn, m0, m2);
    let e = keep(split_first(&[]).map(|(_, t)| t.len()).unwrap_or(77));
    println!("{}", e);
}
