#!/usr/bin/env bash
# scripts/trust_cargo.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Run one Cargo verb with the Trust toolchain's targo. Native compilation
# commands select its explicit UNVERIFIED lane (no proof claim about the build):
#
#   scripts/trust_cargo.sh <verb> [cargo args...] [-- <libtest/program args>]
#
# Noncompiling commands receive no invented compilation authority. `tippy`
# selects its unverified compilation lane internally and rejects that outer
# flag. Unknown commands and unrecognized alias names remain native Targo's
# authorization decision; preserve their arguments and propagate any refusal.
#
# ALab systems build with Trust (owner directive 2026-09-28); there is no stock
# Cargo lane and no fallback to one. targo is $TRUST_TARGO when set (an
# absolute path), else the package `scripts/trust_toolchain.py` resolves from
# PATH (following aterm's atpkg launcher shims) for the `workspace` purpose: the
# root workspace builds against no rustc_private crate, the bridge does.
#
# The installed trustc refuses to run at all while any TRUST_CG_* or TCG_*
# variable is in its environment ("... is an untracked Trust semantic/codegen
# control"), yet the gates' tests read exactly those controls
# (TRUST_CG_RUN_FORMAL_PROOF_TESTS, TRUST_CG_RUN_ROSETTA_LINKRUN, ...). So every
# such variable is removed from targo's environment, and therefore from every
# compiler it runs, and handed back to the executables Cargo runs (tests,
# benches, `run` targets) through a `target.<host>.runner` of
# `/usr/bin/env NAME=VALUE ...`. The runner is Cargo's hook for executing built
# binaries only: the compiler never sees it, while the tests keep Cargo's
# working directory, CARGO_* variables and [env] settings. A trust-cg-verify
# built this way records the Trust sysroot's bin/ay, the one AY its solver
# lanes admit (crates/trust-cg-verify/build.rs).
#
# targo also gets TOOLCHAIN_AY_EXPECTED_SYSROOT, the sysroot of the compiler
# selected here. Cargo keys a build script's compiler by its version text, not
# its path, so two toolchains with byte-identical trustc (two overlays cloned
# from one pack, scripts/assemble_trust_overlay.py) share one fingerprint, and
# trust-cg-verify built for the first would keep the FIRST toolchain's AY
# record. Its build.rs re-records whenever this value changes and records
# nothing when it is not the compiler's sysroot.
set -euo pipefail

if [ "$#" -eq 0 ] || [ -z "${1:-}" ] || [ "${1#-}" != "$1" ]; then
  echo "trust_cargo: usage: trust_cargo.sh <cargo verb> [cargo args...] [-- <args>]" >&2
  exit 2
fi
verb="$1"
shift

# CDPATH=: a relative script directory is never looked up in a CDPATH
# (OD-XHOST-GATE-CWD-20261025, repair round 2).
root="$(CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"

# The python3 every run below starts, resolved once (repair round 3 of
# OD-XHOST-GATE-CWD-20261025): the soundness gate's pinned interpreter when
# the gate started this script (SOUNDNESS_PYTHON3, its canonical path, which
# the gate's host trust boundary judged), else the one PATH finds now. `env`
# below would otherwise look python3 up in the PATH the gate's prelude
# changed.
SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
case "$SOUNDNESS_PYTHON3" in
  /*) ;;
  *)
    echo "trust_cargo: no python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH): '${SOUNDNESS_PYTHON3}'" >&2
    exit 2
    ;;
esac

# Every Trust invocation below runs without the controls trustc refuses.
clean_env=(-u RUSTUP_TOOLCHAIN)
controls=()
while IFS= read -r name; do
  case "$name" in
    TRUST_CG_* | TCG_*)
      clean_env+=(-u "$name")
      controls+=("$name=${!name}")
      ;;
  esac
done < <(compgen -e)

if [ -n "${TRUST_TARGO:-}" ]; then
  targo="$TRUST_TARGO"
  case "$targo" in
    /*) ;;
    *)
      echo "trust_cargo: TRUST_TARGO must be an absolute path, got '$targo'" >&2
      exit 2
      ;;
  esac
  if [ ! -x "$targo" ]; then
    echo "trust_cargo: TRUST_TARGO is not executable: $targo" >&2
    exit 2
  fi
  compiler="$(dirname "$targo")/trustc"
  host=""
  sysroot=""
  if [ -x "$compiler" ]; then
    sysroot="$(env "${clean_env[@]}" "$compiler" --print sysroot 2>/dev/null)" || sysroot=
    # awk reads to EOF: exiting at the first match would SIGPIPE trustc, which
    # still has lines to write, and under pipefail the `|| host=""` below would
    # then erase the triple just read.
    host="$(env "${clean_env[@]}" "$compiler" -vV 2>/dev/null | awk '/^host: / && host == "" { host = $2 } END { print host }')" || host=""
  fi
else
  # Every python3 here runs isolated (-I): `python3 -c` would otherwise put
  # the working directory first on sys.path, and a script run without -I
  # imports from the user site-packages and runs its .pth files
  # (OD-XHOST-GATE-CWD-20261025 and its repair round 2). The resolver uses
  # only the standard library.
  if ! record="$(env "${clean_env[@]}" "$SOUNDNESS_PYTHON3" -I -B "$root/scripts/trust_toolchain.py" --purpose workspace --print json)"; then
    echo "trust_cargo: no installed Trust toolchain resolves (scripts/trust_toolchain.py); there is no stock fallback" >&2
    exit 2
  fi
  targo="$(printf '%s' "$record" | "$SOUNDNESS_PYTHON3" -I -c 'import json, sys; print(json.load(sys.stdin)["targo"])')"
  host="$(printf '%s' "$record" | "$SOUNDNESS_PYTHON3" -I -c 'import json, sys; print(json.load(sys.stdin)["host"])')"
  sysroot="$(printf '%s' "$record" | "$SOUNDNESS_PYTHON3" -I -c 'import json, sys; print(json.load(sys.stdin)["sysroot"])')"
fi
if [ -n "$sysroot" ]; then
  clean_env+=("TOOLCHAIN_AY_EXPECTED_SYSROOT=$sysroot")
fi

config=()
case "$verb" in
  test | t | run | r | bench)
    if [ "${#controls[@]}" -gt 0 ]; then
      if [ -z "$host" ]; then
        echo "trust_cargo: cannot name the host triple to hand ${controls[*]%%=*} to the executables" >&2
        exit 2
      fi
      # macOS: /usr/bin/env is SIP-protected, so dyld strips every DYLD_*
      # variable when Cargo execs it as the runner, and the
      # DYLD_FALLBACK_LIBRARY_PATH Cargo set for the test never reaches it. A
      # test linking rustc_private then aborts with "Library not loaded:
      # @rpath/librustc_driver-*.dylib". Nothing the runner does can recover a
      # value it never received, so hand the child the toolchain's own library
      # directories (and dyld's default fallback list) explicitly.
      dyld=()
      case "$host" in
        *-apple-darwin)
          if [ -n "$sysroot" ]; then
            dyld=("DYLD_FALLBACK_LIBRARY_PATH=$sysroot/lib:$sysroot/lib/rustlib/$host/lib:${HOME:+$HOME/lib:}/usr/local/lib:/usr/lib")
          fi
          ;;
      esac
      runner="$("$SOUNDNESS_PYTHON3" -I -c 'import json, sys
print("target.%s.runner=%s" % (sys.argv[1], json.dumps(["/usr/bin/env"] + sys.argv[2:])))' \
        "$host" ${dyld[@]+"${dyld[@]}"} "${controls[@]}")"
      config=(--config "$runner")
    fi
    ;;
esac

# Public native compilation verbs and their built-in aliases. Never infer
# compilation authority for an unrecognized command name: Targo resolves
# aliases and authorizes the resulting command itself. Noncompiling front doors
# (fetch, metadata, fmt, tippy, trust, ...) must not receive this outer flag.
lane=()
case "$verb" in
  build | b | check | c | fix | clippy | miri | test | t | run | r | bench | \
    doc | d | rustc | rustdoc | install | package | publish)
    lane=(--unverified)
    ;;
esac
exec env "${clean_env[@]}" "$targo" ${lane[@]+"${lane[@]}"} "$verb" ${config[@]+"${config[@]}"} "$@"
