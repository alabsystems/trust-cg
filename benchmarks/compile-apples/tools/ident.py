#!/usr/bin/env python3
"""`.text` identity of two dylibs over the 18-program corpus: sha256 of
objcopy --only-section=.text for every program, both at -O3 (harness lane).
usage: ident.py [--driver TRUSTC] DYLIB_A DYLIB_B   (driver: see _trust_driver.py)"""
import os, subprocess, sys, tempfile, hashlib, glob, shutil
from _trust_driver import resolve_from_argv
home = os.path.expanduser("~")
# STOCK EXCEPTION (Trust lacks rust-lld/gcc-ld; measured: no lib/rustlib/<host>/bin/{rust-lld,gcc-ld} in the Trust sysroot): the Linux linker shim comes from the stock stable toolchain's gcc-ld; the compilers come from the Trust package.
os.environ["PATH"] = f"{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
DRIVER = resolve_from_argv(sys.argv)
a, b = sys.argv[1], sys.argv[2]
rustc = DRIVER["compiler"]
flags = [*DRIVER["compiler_flags"], "--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3"]
progs = sorted(glob.glob(os.environ.get("TCG_PROGS", os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../beat-llvm/progs")) + "/*.rs"))
if not progs:
    raise SystemExit("no corpus programs found")
# The Trust package ships llvm-objcopy in <sysroot>/lib/rustlib/<host>/bin
# (measured); its sysroot comes from the PATH trustc, never a rustup toolchain.
def _trust_llvm_objcopy():
    try:
        sysroot = subprocess.run(["trustc", "--print", "sysroot"], capture_output=True, text=True,
                                 env={k: v for k, v in os.environ.items()
                                      if not k.startswith(("TRUST_CG_", "TCG_"))}).stdout.strip()
    except OSError:
        return None
    return next(iter(glob.glob(f"{sysroot}/lib/rustlib/*/bin/llvm-objcopy")), None) if sysroot else None


OBJCOPY = shutil.which("objcopy") or shutil.which("llvm-objcopy") or _trust_llvm_objcopy()
assert OBJCOPY, "no objcopy"
def text_sha(dylib, p, d):
    out = os.path.join(d, os.path.basename(p)[:-3])
    r = subprocess.run([rustc, f"-Zcodegen-backend={dylib}"] + flags + [p, "-o", out], capture_output=True, text=True)
    if r.returncode: return f"COMPILE-FAIL {r.stderr[-300:]}"
    subprocess.check_call([OBJCOPY, "--only-section=.text", "-O", "binary", out, out + ".text"])
    with open(out + ".text", "rb") as text_section:
        return hashlib.sha256(text_section.read()).hexdigest()
same = 0
with tempfile.TemporaryDirectory() as d:
    adir, bdir = os.path.join(d, "a"), os.path.join(d, "b")
    os.makedirs(adir)
    os.makedirs(bdir)
    for p in progs:
        ha, hb = text_sha(a, p, adir), text_sha(b, p, bdir)
        same += ha == hb
        print(f"{'MATCH   ' if ha == hb else 'DIFFER  '} {os.path.basename(p):32s} {ha[:12]} {hb[:12]}")
print(f"identical: {same}/{len(progs)}")
if same != len(progs):
    raise SystemExit(1)
