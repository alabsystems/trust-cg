#!/usr/bin/env bash
# Linux x86-64 bridge smoke: no_std/no_main compute program, std fn main program.
set -u
S2=$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin
DYLIB=$HOME/trust-cg/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so
T=x86_64-unknown-linux-gnu
D=$(dirname "$0")/work; rm -rf "$D"; mkdir -p "$D"
cat > "$D/compute.rs" <<'RS'
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)]
fn mix(x: u64) -> u64 { x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 7;
    let mut i = 0u32;
    while i < 1000 { acc = mix(acc) ^ (i as u64); i += 1; }
    (acc % 100) as i32
}
RS
cat > "$D/hello.rs" <<'RS'
fn main() {
    let v: Vec<u32> = (0..10).map(|x| x * x).collect();
    let s: u32 = v.iter().sum();
    println!("sum={s}");
    std::process::exit((s % 100) as i32);
}
RS
echo "== oracle (LLVM) compute"; $S2/trustc --edition=2021 -Ztrust-verify=off --crate-type bin --target $T -Cpanic=abort -Coverflow-checks=off -Copt-level=0 --emit=obj -o "$D/compute_llvm.o" "$D/compute.rs" && cc -o "$D/compute_llvm" "$D/compute_llvm.o" && "$D/compute_llvm"; echo "llvm exit=$?"
for opt in 0 1 2 3; do
  echo "== bridge compute O$opt"
  $S2/trustc --edition=2021 -Ztrust-verify=off -Zcodegen-backend=$DYLIB --crate-type bin --target $T -Cpanic=abort -Coverflow-checks=off -Copt-level=$opt --emit=obj -o "$D/compute_tcg$opt.o" "$D/compute.rs" 2> "$D/compute_tcg$opt.err"
  rc=$?; echo "compile rc=$rc"; [ $rc -ne 0 ] && tail -15 "$D/compute_tcg$opt.err"
  if [ $rc -eq 0 ]; then
    obj=$(ls "$D"/compute_tcg$opt*.o 2>/dev/null | head -1); file "$obj"
    nm -u "$obj" | head; cc -o "$D/compute_tcg$opt" "$obj" && "$D/compute_tcg$opt"; echo "bridge O$opt exit=$?"
  fi
done
echo "== oracle hello"; $S2/trustc --edition=2021 -Ztrust-verify=off --target $T -Cpanic=abort -Copt-level=0 -o "$D/hello_llvm" "$D/hello.rs" && "$D/hello_llvm"; echo "llvm exit=$?"
echo "== bridge hello O0 (full link)"
$S2/trustc --edition=2021 -Ztrust-verify=off -Zcodegen-backend=$DYLIB --target $T -Cpanic=abort -Copt-level=0 -o "$D/hello_tcg" "$D/hello.rs" 2> "$D/hello_tcg.err"; rc=$?; echo "compile rc=$rc"
[ $rc -ne 0 ] && tail -25 "$D/hello_tcg.err"
[ $rc -eq 0 ] && { "$D/hello_tcg"; echo "bridge hello exit=$?"; }
