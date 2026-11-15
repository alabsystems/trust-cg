from pathlib import Path
import os,subprocess,json,sys
root=Path('$HOME/trust-cg');r=Path('/home/ayates/trust-cg-soundness-20260914');tc=r/'trust-authored-qualified-20260924/trust-ae9c2c1d'
out=root/'target/reference-raw-reborrow-investigation';backend=r/'current-core-diagnostic-fifty-first/librustc_codegen_trust_cg.so'
env={k:v for k,v in os.environ.items() if not k.startswith(('RUST','CARGO','TRUST','TCG_','AY_')) and k not in ('LD_LIBRARY_PATH','DYLD_LIBRARY_PATH','DYLD_FALLBACK_LIBRARY_PATH')}
env.update(PATH=str(tc/'bin')+':/usr/bin:/bin',RUSTC_BOOTSTRAP='1',RUSTUP_TOOLCHAIN=str(tc),LD_LIBRARY_PATH=str(tc/'lib')+':'+str(tc/'lib/rustlib/aarch64-unknown-linux-gnu/lib'),LC_ALL='C.UTF-8')

private=r/'trust-authored-qualified-20260924/rustc-private-sysroots/rustc-private-tool-stage1-aarch64-unknown-linux-gnu-c10fe5ba8df99cbb'
sdk=r/'trust-main-llvm-sdk-20260925'
target=r/'cg-merged-linux-aggregate-private-target-20260925'
env.update(RUSTC=str(tc/'bin/trustc'),RUSTDOC=str(tc/'bin/trustdoc'),CARGO_TARGET_DIR=str(target),CARGO_BUILD_JOBS='2',CARGO_INCREMENTAL='0',RUST_MIN_STACK='16777216',RUST_TEST_THREADS='1',RUSTFLAGS=f'-Lall={private}/aarch64-unknown-linux-gnu -Lall={private}/host -Lnative={sdk}/lib',LLVM_CONFIG=str(sdk/'bin/llvm-config'))

