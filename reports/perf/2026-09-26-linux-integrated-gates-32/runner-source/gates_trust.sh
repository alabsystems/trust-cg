#!/bin/bash
# Integration gates in explicit Trust development mode (Trust ae9c2c1da).
# Usage: gates_trust.sh <tag>   (writes $F/<name>-<tag>.log and $F/gates-<tag>.status)
T=$1
F=/home/ayates/trust-cg-floor-20260922
S=/tmp/claude-1000/-home-ayates-trust-cg/5c614a35-bd1c-42d4-a526-64c88f7a04db/scratchpad
TC=/home/ayates/toolchains/trust-ae9c2c1d
TOOLS=$HOME/.local/lib/trust-cg/ae9c2c1d-tools
ST=$F/gates-$T.status
DIR=${2:-/home/ayates/trust-cg-wt/integ-live}
SKIP_FLOOR=${SKIP_FLOOR:-0}
cd $DIR
BASE_ENV="env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTC_WRAPPER -u TCG_REQUIRE_LLD -u TCG_REQUIRE_GOLD -u TCG_EXTERNAL_CLEAN_CHECKER"
export PATH="$TC/bin:$TOOLS/bin:$HOME/.cargo/bin:$PATH"
TARGO="$BASE_ENV RUSTC=$TC/bin/trustc RUSTDOC=$TC/bin/trustdoc targo --unverified"
LINKERS="CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER=$S/require-linkers-runner.sh"
: > $ST
[ "$SKIP_FLOOR" = 1 ] || $BASE_ENV python3 -B scripts/check_linux_aarch64.py --trust-unverified --require-clean --max-rss-gib 16 --require-offline-deps --require-proof-tools --jobs 2 --out $F/run-$T > $F/floor-$T.log 2>&1
echo "floor-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-codegen -p trust-cg-lower --lib > $F/lib-$T.log 2>&1
echo "lib-exit=$?" >> $ST
env $LINKERS $TARGO test --locked --offline -j 8 -p trust-cg-cli --bins --test link_options --test output_paths --test trust_ir_binary_container > $F/cli-bin-$T.log 2>&1
echo "cli-bin-exit=$?" >> $ST
env $LINKERS $TARGO test --locked --offline -j 8 -p trust-cg-codegen --test e2e_aarch64_link_runtime --test e2e_aarch64_elf_tlsie --test e2e_aarch64_eh_linux --test e2e_aarch64_eh_catch --test aarch64_elf_cfi_differential --test e2e_aarch64_elf_link -- --nocapture > $F/natives-$T.log 2>&1
echo "natives-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-verify --test fsym_ub_map --test fsym_interpreter_oracle > $F/fsym-$T.log 2>&1
echo "fsym-verify-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-cli --test fsym_flag > $F/fsym-cli-$T.log 2>&1
echo "fsym-cli-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-opt --lib > $F/opt-lib-$T.log 2>&1
echo "opt-lib-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-codegen --test jit_external_symbol_resolution_policy --test core_jit_planning --test e2e_x86_64_module_batch_fnptr --test e2e_x86_64_module_batch_globals > $F/localcall-$T.log 2>&1
echo "localcall-exit=$?" >> $ST
env $LINKERS $TARGO test --locked --offline -j 8 -p trust-cg-codegen --test aarch64_elf_symbol_binding --test e2e_aarch64_elf_relocation_model -- --nocapture > $F/binding-$T.log 2>&1
echo "binding-exit=$?" >> $ST
$TARGO test --locked --offline -j 8 -p trust-cg-verify --test coverage_gate_tests --test aarch64_value_decode_gate --test proof_gate_strict --test soundness_manifest --test meta_theorems > $F/verify-gates-$T.log 2>&1
echo "verify-gates-exit=$?" >> $ST
$BASE_ENV PATH="$HOME/.cargo/bin:$PATH" cargo run --locked --offline -j 8 -p trust-cg-test --quiet -- ratchet unwrap > $F/ratchet-$T.log 2>&1
echo "ratchet-exit=$?" >> $ST
[ "$SKIP_FLOOR" = 1 ] || $BASE_ENV PATH="/home/ayates/toolchains/trust-a62ae50d/bin:$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin:$HOME/.cargo/bin:$PATH" python3 -B scripts/check_linux_aarch64_bridge.py --require-proof-tools --out $F/bridge-$T --target-dir /home/ayates/trust-cg-wt/integ-live-bridge-target --jobs 4 --timeout-seconds 7200 > $F/bridge-$T.log 2>&1
echo "bridge-exit=$?" >> $ST
echo DONE >> $ST
