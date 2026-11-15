#!/bin/zsh
# Release bridge build for trees whose AY pin needs the Trust 0.11 manifest surface
# (AY 7ed2ea1da and later: `[trust] backstop`, which the d7f143f3b stage-1 targo refuses as
# "unknown field"). Same compiler, sysroot and AY/Clean pair as build_bridge.ay13556.sh; only
# the targo that DRIVES the build differs:
#   targo  = ~/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo, an engineering
#            build of Trust 13bb1758dc's src/tools/targo (x.py targo-build-tool, compiler0 =
#            the d7f143f3b native stage-1; ~/tcg-scratch/trust-t011/README.md);
#   RUSTC  = ~/.local/share/trust-overlays/x86-stage0-bridge-ay13556-t011/bin/trustc, the
#            pack 6808 trustc wrapper over the stage-1 build's stage0-sysroot clone, whose
#            bin/ay is AY 0.27.0 build 13556 (ebde49de3) and bin/clean is Clean 5f09e36c.
# Run the census on the ROOT t011 overlay's trustc (census_t011.sh): a bridge loaded into a
# compiler admits that compiler's sysroot bin/ay, which must be the recorded build 13556.
# Lane: targo --unverified (no proof claim about the build; the targo is local, uncertified).
# Older trees (AY 630842a/8e7b3fe, `compiler_timeout_secs`) keep build_bridge.ay13556.sh, the
# lane their records were made on. (The 13bb1758dc targo reads those manifests too, measured
# 2026-11-02 on b4954b8e4, but nothing was built or qualified with it on such a tree.)
cd "${1:?worktree}/crates/rustc-codegen-trust-cg" || exit 9
ROOT_OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
BRIDGE_OVERLAY=$HOME/.local/share/trust-overlays/x86-stage0-bridge-ay13556-t011
[ -x "$ROOT_OVERLAY/bin/targo" ] && [ -x "$BRIDGE_OVERLAY/bin/trustc" ] || { echo "build_bridge.t011: overlay missing"; exit 9; }
export RUSTC=$BRIDGE_OVERLAY/bin/trustc
# Forces trust-cg-verify's build.rs to re-record when the selected sysroot changes (and
# records nothing if the compiler reports another sysroot).
export TOOLCHAIN_AY_EXPECTED_SYSROOT=$BRIDGE_OVERLAY
nice "$ROOT_OVERLAY/bin/targo" --unverified build --release --locked -j2 2>&1 | grep -E '^error|^warning: unused|Finished|could not compile' | head -20
echo "EXIT=${pipestatus[1]}"
