#!/usr/bin/env bash
#
# soundness_remote.sh — run the x86_64-native soundness legs on a native x86-64
# host and import that host's attestation record.
#
#   scripts/soundness_remote.sh probe --repo <trust-cg> --host <ssh destination>
#   scripts/soundness_remote.sh run   --repo <trust-cg> --host <ssh destination> \
#                                     --commit <40-hex C> --out <dir>
#
# soundness_check.sh calls `probe` in its preflight and `run` in the background
# of a full run on a host that is not native x86-64 (see its HOST CLASSES).
#
# `probe` checks, over ssh with BatchMode and a connect timeout, what those legs
# need on the remote: an x86-64 machine that is not translated (Rosetta), git,
# python3, the toolchain the candidate's rust-toolchain.toml pins (for
# `channel = "trust"`, a Trust package on PATH: a branded trustc with a 40-hex
# commit identity and targo beside it), clang as `cc` (e2e_x86_64_swiftcc
# SKIPs under GCC, XD-03), an LLVM-family objdump (e2e_x86_64_callee_saved (E2)
# decodes Mach-O and ELF; GNU objdump SKIPs it), and read access to the
# first-party dependency repositories Cargo fetches (trust-ir, clean, ay).
# CPUID-level emulation detection runs in the remote gate's own preflight
# (scripts/soundness_attestation.py host), which refuses QEMU/TCG CPUs.
#
# `run` sends commit C as a git bundle (incremental against what the remote
# clone already has), checks C out DETACHED in a dedicated clone
# (SOUNDNESS_X86_REMOTE_DIR, default ~/.cache/trust-cg/soundness-remote/trust-cg
# on the remote; an absolute path, "~/..." or a path relative to the remote
# HOME, spaces allowed), refuses a tree that is not C^{tree}, runs
#   scripts/soundness_check.sh --attest --host-legs x86_64-native
# there, and brings the record ref refs/attest/soundness/<C>/<x86 triple> back as
# a bundle. The imported record is re-checked locally (single parent C, subject
# tree, host triple, native x86-64 host fields, every leg PASS) and STAGED at
# refs/soundness/import/<C>/<triple> before <out>/record_oid, <out>/triple and
# <out>/status are written; the gate publishes it under refs/attest/ only in
# the same atomic write as its own green record. Any failure,
# including an unreachable host, exits nonzero: the caller records a FAIL,
# never a SKIP. A record already present locally for C on an x86-64 triple that
# passes the same check is reused (same commit only).
#
# Every directory this script creates on the remote under ~/.cache/trust-cg
# (the clone's directory, incoming/) is 0700 whatever the remote umask, by the
# rule of scripts/private_cache.py, whose source is sent with the remote
# script (the remote has no checkout of its own yet). An existing directory is
# never changed. Everything the run phase writes after that (the clone, the
# x86-64 legs' build tree and Python caches in it, the record bundle) and
# every bundle send_file writes is written under umask 077, so nothing under
# the remote cache follows the remote login umask. AY's private copy lives
# under the same ~/.cache/trust-cg and is refused while it or an ancestor is
# group-writable, so a `mkdir -p` under the remote's umask 0002 refused AY for
# the legs run there (X-HOST-P13).
#
# The remote host is trusted to run the legs it reports; its record is
# unsigned today (see SOUNDNESS_CHECK.md, "Attestation records").
set -u
set -o pipefail

SSH_COMMAND="${SOUNDNESS_SSH:-ssh}"
CONNECT_TIMEOUT="${SOUNDNESS_SSH_CONNECT_TIMEOUT:-15}"
REMOTE_DIR="${SOUNDNESS_X86_REMOTE_DIR:-}"
# The stock toolchain the candidate pins; the remote must provide exactly it.
EXPECTED_RUST=""

die() { printf 'soundness_remote: %s\n' "$*" >&2; exit 1; }

phase="${1:-}"
[ "$#" -gt 0 ] && shift
repo="" host="" commit="" out=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --repo) repo="${2:-}"; shift ;;
    --host) host="${2:-}"; shift ;;
    --commit) commit="${2:-}"; shift ;;
    --out) out="${2:-}"; shift ;;
    *) printf 'soundness_remote: unknown argument %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done
case "$phase" in
  probe) [ -n "$repo" ] && [ -n "$host" ] || { echo "usage: probe --repo R --host H" >&2; exit 2; } ;;
  run) [ -n "$repo" ] && [ -n "$host" ] && [[ "$commit" =~ ^[0-9a-f]{40}$ ]] && [ -n "$out" ] ||
         { echo "usage: run --repo R --host H --commit <40-hex> --out DIR" >&2; exit 2; } ;;
  *) echo "usage: soundness_remote.sh probe|run ..." >&2; exit 2 ;;
esac
# Every argument of a remote phase reaches the remote as part of ONE command
# line that the remote login shell parses (ssh joins its arguments), quoted
# here by bash's printf %q. For a control character, and for a non-ASCII byte
# under a C locale, %q emits bash's $'...' form, which a POSIX login shell
# such as dash reads literally; and bash escapes a quote inside it as \', which
# dash does not honor, so a SOUNDNESS_X86_REMOTE_DIR holding a tab and a quote
# ran the rest of its value as commands there (X-HOST-P13 second audit). An
# argument is therefore sent only when every character is one of
# SAFE_REMOTE_CHARACTERS (listed one by one, so no locale's collation can
# widen a range), for which %q emits at most a backslash escape, read alike by
# every POSIX shell; any other value is refused by name.
SAFE_REMOTE_CHARACTERS='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 ~/._+,:@=-'
require_safe_remote_word() {
  # require_safe_remote_word <name> <value>
  local value="$2" index character
  for ((index = 0; index < ${#value}; index++)); do
    character="${value:index:1}"
    case "$SAFE_REMOTE_CHARACTERS" in
      *"$character"*) ;;
      *) die "$1 holds a character outside [A-Za-z0-9 ~/._+,:@=-] ($(printf '%q' "$character")): refused, because the remote login shell would not read $1 as one word" ;;
    esac
  done
}
require_safe_remote_word SOUNDNESS_X86_REMOTE_DIR "$REMOTE_DIR"
TOOL="${repo}/scripts/soundness_attestation.py"
PRIVATE_CACHE_SOURCE="$(cat "${repo}/scripts/private_cache.py" 2>/dev/null)" && [ -n "$PRIVATE_CACHE_SOURCE" ] ||
  die "cannot read ${repo}/scripts/private_cache.py"
EXPECTED_RUST="$(sed -nE 's/^channel[[:space:]]*=[[:space:]]*"([^"]+)"[[:space:]]*$/\1/p' "$repo/rust-toolchain.toml" 2>/dev/null)"
[ "$(printf '%s\n' "$EXPECTED_RUST" | grep -c .)" -eq 1 ] ||
  die "$repo/rust-toolchain.toml does not name exactly one channel"

ssh_remote() {
  # ssh_remote <remote argv...>; stdin passes through.
  # shellcheck disable=SC2086  # SOUNDNESS_SSH may carry options
  $SSH_COMMAND -o BatchMode=yes -o ConnectTimeout="$CONNECT_TIMEOUT" \
    -o ServerAliveInterval=30 -o ServerAliveCountMax=4 "$host" "$@"
}

dependency_urls() {
  # The first-party Git sources the candidate's root lock names.
  sed -nE 's|^[[:space:]]*source = "git\+(https://github\.com/[^/]+/(trust-ir\|clean\|ay)\.git)\?rev=.*$|\1|p' \
    "$repo/Cargo.lock" | sort -u
}

# The remote side. It runs under the remote user's login shell as `bash -s`;
# its first argument is the phase and the rest are phase arguments.
REMOTE_SCRIPT='
remote_main() {
set -u
phase="$1"; shift
remote_dir="${1:-}"; shift
# home_path PATH: PATH with a leading "~" or "~/" read as the remote HOME, and
# a relative PATH read below the remote HOME. The phase arguments arrive
# quoted, so the remote shell never expands a "~" in them itself.
home_path() {
  case "$1" in
    /*) printf "%s\n" "$1" ;;
    "~") printf "%s\n" "$HOME" ;;
    "~/"*) printf "%s\n" "$HOME/${1#"~/"}" ;;
    *) printf "%s\n" "$HOME/$1" ;;
  esac
}
if [ -n "$remote_dir" ]; then
  remote_dir="$(home_path "$remote_dir")"
else
  remote_dir="$HOME/.cache/trust-cg/soundness-remote/trust-cg"
fi
fail() { printf "REMOTE-FAIL: %s\n" "$*"; exit 1; }
# private_mkdir DIR...: scripts/private_cache.py (its source is $private_cache_py):
# each directory it creates is 0700 whatever the umask; existing ones are left.
private_mkdir() {
  python3 -I -c "$private_cache_py" mkdir "$@" || return 1
  for dir in "$@"; do [ -d "$dir" ] || return 1; done
}
incoming_dir="$(home_path "$incoming")"
case "$phase" in
  probe)
    expected_rust="$1"; shift
    problems=""
    machine="$(uname -m)"
    case "$machine" in x86_64|amd64) ;; *) problems="$problems machine=$machine;" ;; esac
    if [ "$(uname -s)" = Darwin ] && [ "$(sysctl -n sysctl.proc_translated 2>/dev/null)" = 1 ]; then
      problems="$problems translated(Rosetta);"
    fi
    for tool in git python3; do
      command -v "$tool" >/dev/null 2>&1 || problems="$problems no-$tool;"
    done
    if [ "$expected_rust" = trust ]; then
      # The Trust package on PATH (scripts/trust_toolchain.py resolves it there
      # and scripts/trust_cargo.sh runs its targo): a branded trustc with a
      # 40-hex commit identity, and targo beside it.
      for tool in trustc targo; do
        command -v "$tool" >/dev/null 2>&1 || problems="$problems no-$tool;"
      done
      identity="$(trustc -vV 2>/dev/null || true)"
      printf "%s\n" "$identity" | grep -qx "binary: trustc" || problems="$problems trustc-not-branded;"
      printf "%s\n" "$identity" | grep -Eqx "commit-hash: [0-9a-f]{40}" || problems="$problems trustc-no-commit-identity;"
    elif ! command -v rustup >/dev/null 2>&1; then
      problems="$problems no-rustup;"
    elif ! rustup toolchain list 2>/dev/null | grep -q "^$expected_rust"; then
      problems="$problems no-rust-$expected_rust;"
    fi
    cc --version 2>/dev/null | grep -qi clang || problems="$problems cc-is-not-clang;"
    if ! { llvm-objdump --version 2>/dev/null || objdump --version 2>/dev/null; } | grep -qi llvm; then
      problems="$problems no-llvm-objdump;"
    fi
    for url in "$@"; do
      GIT_TERMINAL_PROMPT=0 git ls-remote --exit-code "$url" HEAD >/dev/null 2>&1 ||
        problems="$problems cannot-read-$url;"
    done
    private_mkdir "$remote_dir" "$incoming_dir" 2>/dev/null || problems="$problems cannot-create-$remote_dir;"
    [ -z "$problems" ] || fail "x86-64 executor requirements:$problems"
    echo "REMOTE-OK $(uname -sm) $(cc --version 2>/dev/null | head -1)"
    ;;
  tips)
    if [ -d "$remote_dir/.git" ]; then
      git -C "$remote_dir" for-each-ref --format="%(objectname)" refs/soundness refs/heads 2>/dev/null
    fi
    ;;
  run)
    commit="$1"; tree="$2"; bundle_path="$(home_path "$3")"
    private_mkdir "$remote_dir" || fail "cannot create $remote_dir"
    # Everything from here on (the clone, the x86-64 legs and their build
    # tree, the record bundle) is written under umask 077.
    umask 077
    # The clone is entered ONCE, by its physical path (cd -P), and named only
    # relative to that directory afterwards: the tree checked below, the legs
    # run from it and the TRUST_CG_DIR of the gate there (its pwd) are one
    # directory, whatever symlink $remote_dir ran through (X-HOST-P13 third
    # closure audit: a name checked through a re-pointable symlink is not the
    # directory used).
    CDPATH= cd -P -- "$remote_dir" || fail "no remote clone at $remote_dir"
    [ -d .git ] || git init -q . || fail "cannot create a clone at $remote_dir"
    git fetch -q "$bundle_path" "refs/soundness/dispatch/$commit:refs/soundness/candidate/$commit" ||
      fail "cannot fetch the bundle"
    [ -z "$(git status --porcelain)" ] || fail "the dedicated remote clone $remote_dir is dirty"
    git -c advice.detachedHead=false checkout -q --detach "$commit" || fail "cannot check out $commit"
    [ "$(git rev-parse HEAD)" = "$commit" ] || fail "HEAD is not $commit"
    [ "$(git rev-parse "HEAD^{tree}")" = "$tree" ] || fail "tree mismatch: remote $(git rev-parse "HEAD^{tree}") != $tree"
    unset SOUNDNESS_X86_HOST
    # The relative name is the clone entered above: soundness_check.sh finds
    # its own directory with CDPATH ignored and refuses one that does not hold
    # the file bash runs (OD-XHOST-GATE-CWD-20261025, repair round 2).
    bash scripts/soundness_check.sh --attest --host-legs x86_64-native || fail "the x86-64-native legs did not pass (rc=$?)"
    refs="$(git for-each-ref --format="%(refname)" "refs/attest/soundness/$commit/")"
    [ "$(printf "%s\n" "$refs" | grep -c .)" -eq 1 ] || fail "expected exactly one record ref for $commit, found: $refs"
    record_bundle="$(dirname "$bundle_path")/record-$commit.bundle"
    git bundle create -q "$record_bundle" "$refs" "^$commit" || fail "cannot bundle the record"
    echo "REMOTE-RECORD $refs $(git rev-parse "$refs") $record_bundle"
    ;;
  *) fail "unknown phase $phase" ;;
esac
}
remote_main "$@" </dev/null
'

# The python3 the local half starts (the record check below), resolved once
# (repair round 3 of OD-XHOST-GATE-CWD-20261025): the soundness gate's pinned
# interpreter when the gate started this script (SOUNDNESS_PYTHON3, its
# canonical path, which the gate's host trust boundary judged), else the one
# PATH finds now. REMOTE_SCRIPT above runs on the remote host with the
# remote's own python3; the remote gate pins its own interpreter.
SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
case "$SOUNDNESS_PYTHON3" in
  /*) ;;
  *) die "no python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH): '${SOUNDNESS_PYTHON3}'" ;;
esac

# Bundles move as plain byte streams. Their remote paths are fixed strings plus
# a 40-hex commit id, so they need no quoting beyond the single quotes below.
INCOMING=".cache/trust-cg/soundness-remote/incoming"

remote() {
  # remote <phase> [args...]: run one phase of REMOTE_SCRIPT on the host. The
  # script is read whole (one function) before it runs, and its commands read
  # /dev/null, so nothing it starts can consume the script from stdin. Its
  # prelude carries the private-cache rule's source and the incoming
  # directory. ssh joins its arguments into ONE command line for the remote
  # shell, which would drop an empty argument (an unset
  # SOUNDNESS_X86_REMOTE_DIR) and shift every later one, so the arguments are
  # quoted into that line here.
  local phase="$1" prelude argument position=0
  shift
  for argument in "$phase" "$REMOTE_DIR" "$@"; do
    position=$((position + 1))
    require_safe_remote_word "remote argument ${position}" "$argument"
  done
  prelude="$(printf 'private_cache_py=%q\nincoming=%q\n' "$PRIVATE_CACHE_SOURCE" "$INCOMING")"
  printf '%s\n%s' "$prelude" "$REMOTE_SCRIPT" |
    ssh_remote "bash -s --$(printf ' %q' "$phase" "$REMOTE_DIR" "$@")"
}

# The probe created the incoming directory by the private-cache rule; under
# umask 077 this `mkdir -p` can only create private directories and the bundle
# is written 0600.
send_file() { ssh_remote "umask 077 && mkdir -p '$INCOMING' && cat > '$INCOMING/$1'"; }
receive_file() { ssh_remote "cat '$1'"; }

probe() {
  local urls output
  urls="$(dependency_urls)"
  # shellcheck disable=SC2086  # one URL per word
  if ! output="$(remote probe "$EXPECTED_RUST" $urls 2>&1)"; then
    printf '%s\n' "$output"
    die "x86-64 executor ${host} is unreachable or unqualified"
  fi
  printf '%s\n' "$output"
  printf '%s\n' "$output" | grep -q '^REMOTE-OK' || die "x86-64 executor ${host} gave no REMOTE-OK"
}

if [ "$phase" = probe ]; then
  probe
  exit $?
fi

# ---------------------------------------------------------------- run
mkdir -p "$out" || die "cannot create $out"
printf '1\n' >"$out/status"
child=""
cleanup() {
  # The remote step runs in its own process group (set -m below): stop all of
  # it, ssh included. A remote command may still run on the host until its
  # next write to the closed connection fails.
  [ -z "$child" ] || kill -TERM -- "-$child" 2>/dev/null || kill -TERM "$child" 2>/dev/null || :
  git -C "$repo" update-ref -d "refs/soundness/dispatch/$commit" 2>/dev/null || :
}
trap 'cleanup; exit 143' TERM INT
trap cleanup EXIT

tree="$(git -C "$repo" rev-parse --verify "${commit}^{tree}")" || die "unknown commit $commit"

accept_record() {
  # accept_record <triple> <oid>: the local checks every imported record passes.
  local triple="$1" oid="$2"
  case "$triple" in x86_64-*) ;; *) echo "record triple $triple is not x86-64"; return 1 ;; esac
  # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025).
  "$SOUNDNESS_PYTHON3" -I "$TOOL" check-record --repo "$repo" --record "$oid" --commit "$commit" --triple "$triple" \
    --scope x86_64-native
}

# Same-commit reuse: a record already published or staged for C that passes the checks.
while read -r ref oid; do
  [ -n "${ref:-}" ] || continue
  triple="${ref##*/}"
  if accept_record "$triple" "$oid" >/dev/null 2>&1; then
    printf '%s\n' "$oid" >"$out/record_oid"
    printf '%s\n' "$triple" >"$out/triple"
    printf '0\n' >"$out/status"
    echo "reusing the x86-64 record already present for ${commit}: ${ref} ${oid}"
    exit 0
  fi
done < <(git -C "$repo" for-each-ref --format='%(refname) %(objectname)' \
  "refs/attest/soundness/${commit}/x86_64-*" "refs/soundness/import/${commit}/x86_64-*")

probe || exit 1

bundle="${out}/candidate.bundle"
remote_bundle="${INCOMING}/${commit}.bundle"
git -C "$repo" update-ref "refs/soundness/dispatch/$commit" "$commit" || die "cannot create the dispatch ref"
have=()
while read -r tip; do
  [[ "$tip" =~ ^[0-9a-f]{40}$ ]] || continue
  # A tip that already contains C would empty the bundle; send C's history then.
  git -C "$repo" cat-file -e "${tip}^{commit}" 2>/dev/null || continue
  git -C "$repo" merge-base --is-ancestor "$commit" "$tip" 2>/dev/null && continue
  have+=("^$tip")
done < <(remote tips 2>/dev/null || true)
git -C "$repo" bundle create -q "$bundle" "refs/soundness/dispatch/$commit" ${have[@]+"${have[@]}"} ||
  die "cannot bundle $commit"
send_file "${commit}.bundle" <"$bundle" || die "cannot send the bundle to $host"

run_output="${out}/remote-run.log"
set -m
remote run "$commit" "$tree" "$remote_bundle" >"$run_output" 2>&1 &
child=$!
set +m
wait "$child"
rc=$?
child=""
tail -40 "$run_output"
[ "$rc" -eq 0 ] || die "remote x86-64-native run failed (rc=$rc); see $run_output"
line="$(grep '^REMOTE-RECORD ' "$run_output" | tail -1)"
[ -n "$line" ] || die "remote run reported no record"
read -r _ record_ref record_oid record_bundle <<<"$line"
triple="${record_ref##*/}"
[ "$record_ref" = "refs/attest/soundness/${commit}/${triple}" ] || die "unexpected record ref $record_ref"
[[ "$record_oid" =~ ^[0-9a-f]{40}$ ]] || die "malformed record id $record_oid"
local_bundle="${out}/record.bundle"
case "$record_bundle" in
  */"${INCOMING}/record-${commit}.bundle") ;;
  *) die "unexpected record bundle path $record_bundle" ;;
esac
receive_file "${INCOMING}/record-${commit}.bundle" >"$local_bundle" || die "cannot fetch the record bundle"
# The record is STAGED, not published: refs/soundness/import/<C>/<triple>
# keeps its objects reachable, and the gate's own `soundness_attestation.py
# write` creates ${record_ref} together with the local record in one atomic
# ref transaction. A run that stops before that write leaves no record under
# refs/attest/ (the gate deletes the staging ref).
staging_ref="refs/soundness/import/${commit}/${triple}"
git -C "$repo" fetch -q "$local_bundle" "+${record_ref}:${staging_ref}" ||
  die "cannot import the record bundle"
imported="$(git -C "$repo" rev-parse --verify "$staging_ref")"
[ "$imported" = "$record_oid" ] || die "imported record $imported is not the reported $record_oid"
accept_record "$triple" "$record_oid" || die "the imported record failed its local checks"
printf '%s\n' "$record_oid" >"$out/record_oid"
printf '%s\n' "$triple" >"$out/triple"
printf '0\n' >"$out/status"
echo "staged ${staging_ref} ${record_oid} (the gate's record write publishes it as ${record_ref})"
