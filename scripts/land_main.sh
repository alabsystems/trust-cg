#!/usr/bin/env bash
#
# land_main.sh — the serialized landing train for trust-cg `main`.
#
#   scripts/land_main.sh [--source-only --source-check 'PROGRAM ARG...'] [--resume-source-candidate SHA] [--remote NAME] [--worktree DIR] [--attempts N] [--no-push] <lane-ref>...
#
# --source-only publishes ordinary development source after tracked-path and
# explicitly named focused checks. Repeat --source-check for each command;
# arguments are split with Python shlex, with no shell expansion. The checks
# must cover changed source/behavior and applicable proof/certificate paths.
# --resume-source-candidate SHA keeps an explicit existing clean worktree at
# that exact commit; fresh main and all lanes must already be its ancestors.
# It neither runs nor claims the full attestation campaign, creates no proof
# records and grants no landing/release verdict. The default attested mode
# below remains unchanged. Owner ordinary-source directive 2026-11-02.
#
# Gating every push with the full soundness gate livelocks while main moves
# faster than one gate cycle. The train instead lands a BATCH per cycle:
#
#   1. take the train lease (one train per clone; a local lock, see below);
#   2. fetch <remote>/main and check out that base DETACHED in a dedicated,
#      clean train worktree (default: <git-common-dir>/land-main-worktree);
#   3. merge every queued lane ref into it, in order (--no-ff; a conflict stops
#      the train with nothing pushed and names the lane);
#   4. run C's actual path-collision, trustfmt and tippy hook pre-flights
#      BEFORE the proof campaign (the final push hook still runs them), then
#      run the merge result C's own scripts/soundness_check.sh --attest, which
#      writes C's records under refs/attest/soundness/<C>/ locally. The run is
#      `--scope portable` when the base's verifier defers the x86-64-native
#      class for landing (its DEFERRED_LANDING_CLASSES) and this host has no
#      x86-64 executor (not native x86-64, SOUNDNESS_X86_HOST unset);
#   5. give C the LANDING verdict (`verify --landing`) of the verifier
#      committed at the base, extracted from the base's tree and run directly
#      (C's scripts/soundness_attestation.py does not run; C's
#      soundness_check.sh --list-json does, to declare C's inventory, which the
#      base's verifier holds to the base's). A base without a committed
#      verifier (the bootstrap) stops the train;
#   6. explicitly run the mandatory pre-push hook (native agh disables hooks),
#      then push main and its records in ONE native agh atomic leased batch;
#   7. if main moved meanwhile, the fast-forward push is rejected: re-fetch,
#      re-merge on the new base and run the gate again (a new C is a new
#      commit; no result is reused across commits), up to --attempts times.
#
# A gate failure, a failed verification or an exhausted retry budget pushes
# nothing. --no-push stops after step 5 (a dry run that still attests).
#
# The lease serializes trains of this clone (a lock directory holding the
# owner's pid under the Git common directory; a lease whose pid is gone is
# reclaimed). Independent clones, including on the SAME machine, have distinct
# leases. Atomic fast-forward push serializes commit updates, not gate work:
# at most one concurrent push wins, but this does not guarantee progress for a
# slower train while other writers keep advancing main. A cross-clone batch
# queue needs one designated publisher; this script does not implement one.
# Never run it in a shared lane worktree.
#
set -u
set -o pipefail

remote="origin"
worktree=""
worktree_explicit=0
resume_source_candidate=""
attempts=3
push=1
source_only=0
source_checks=()
lanes=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --remote) remote="${2:?--remote needs a name}"; shift ;;
    --worktree) worktree="${2:?--worktree needs a directory}"; worktree_explicit=1; shift ;;
    --resume-source-candidate) resume_source_candidate="${2:?--resume-source-candidate needs a full commit SHA}"; shift ;;
    --attempts) attempts="${2:?--attempts needs a number}"; shift ;;
    --no-push) push=0 ;;
    --source-only) source_only=1 ;;
    --source-check) source_checks+=("${2:?--source-check needs a command}"); shift ;;
    -h|--help) awk 'NR == 1 { next } !/^#/ { exit } { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    -*) echo "land_main: unknown option $1" >&2; exit 2 ;;
    *) lanes+=("$1") ;;
  esac
  shift
done
[ "${#lanes[@]}" -gt 0 ] || { echo "land_main: name at least one lane ref to land" >&2; exit 2; }
[[ "$attempts" =~ ^[1-9][0-9]*$ ]] || { echo "land_main: --attempts must be a positive integer" >&2; exit 2; }
if [ "$source_only" -eq 1 ]; then
  [ "${#source_checks[@]}" -gt 0 ] || { echo "land_main: --source-only requires focused --source-check commands" >&2; exit 2; }
elif [ "${#source_checks[@]}" -gt 0 ]; then
  echo "land_main: --source-check requires --source-only" >&2; exit 2
fi

# A source-only continuation keeps one existing candidate immutable. Fresh
# authenticated main and every declared lane must already be ancestors.
if [ -n "$resume_source_candidate" ]; then
  if [ "$source_only" -ne 1 ] || [ "$worktree_explicit" -ne 1 ] || [ -z "$worktree" ]; then
    echo "land_main: --resume-source-candidate requires --source-only and an explicit existing --worktree" >&2
    exit 2
  fi
  if ! [[ "$resume_source_candidate" =~ ^[0-9a-f]{40}$ ]]; then
    echo "land_main: --resume-source-candidate requires a full lowercase commit SHA" >&2
    exit 2
  fi
fi

say() { printf 'land_main: %s\n' "$*"; }
die() { printf 'land_main: %s\n' "$*" >&2; exit 1; }

# The python3 the train starts (the base's verifier), resolved once, by an
# absolute path, before anything runs (repair round 3 of
# OD-XHOST-GATE-CWD-20261025): SOUNDNESS_PYTHON3 when the caller exported one,
# else the one PATH finds now. It is not exported to the gate, which pins its
# own interpreter and refuses a caller's SOUNDNESS_PYTHON3.
SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
case "$SOUNDNESS_PYTHON3" in
  /*) ;;
  *)
    echo "land_main: no python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH): '${SOUNDNESS_PYTHON3}'" >&2
    exit 2
    ;;
esac

repo="$(git rev-parse --show-toplevel)" || die "not inside a Git checkout"
# `CDPATH= cd --` throughout: `git rev-parse --git-common-dir` prints `.git`
# at a main checkout's top, which a plain `cd` would first look up in an
# exported CDPATH, putting the lease and the train worktree in another
# directory (OD-XHOST-GATE-CWD-20261025, repair round 2).
common="$(CDPATH= cd -- "$repo" && CDPATH= cd -- "$(git rev-parse --git-common-dir)" && pwd)" ||
  die "no Git common directory"
# A relative --worktree names a directory relative to where the train was
# started; it is made absolute now, since `git -C "$repo" worktree add` would
# resolve it in $repo and `cd` in the working directory.
case "$worktree" in
  ""|/*) ;;
  *) worktree="${PWD}/${worktree}" ;;
esac
[ -n "$worktree" ] || worktree="${common}/land-main-worktree"

# Resolve every lane to a commit now, so the batch cannot drift while it lands.
lane_commits=()
for lane in "${lanes[@]}"; do
  sha="$(git -C "$repo" rev-parse --verify --quiet "${lane}^{commit}")" || die "unknown lane ref: $lane"
  lane_commits+=("$sha")
done

# --- the lease ------------------------------------------------------------
lease="${common}/land-main.lease"
if ! mkdir "$lease" 2>/dev/null; then
  holder="$(cat "$lease/pid" 2>/dev/null || true)"
  if [ -n "$holder" ] && kill -0 "$holder" 2>/dev/null; then
    die "another landing train holds the lease (pid $holder, $lease)"
  fi
  say "reclaiming a stale lease left by pid ${holder:-unknown}"
  rm -rf "${lease:?}"
  mkdir "$lease" || die "cannot take the lease $lease"
fi
printf '%s\n' "$$" >"$lease/pid"
trap 'rm -rf "${lease:?}"' EXIT
trap 'exit 130' INT TERM

# --- the dedicated worktree -------------------------------------------------
if [ ! -e "$worktree/.git" ]; then
  [ -z "$resume_source_candidate" ] || die "source resume requires an existing worktree; candidate was not recreated"
  git -C "$repo" worktree add --quiet --detach "$worktree" HEAD >/dev/null || die "cannot create $worktree"
fi
wt_common="$(CDPATH= cd -- "$worktree" && CDPATH= cd -- "$(git rev-parse --git-common-dir)" && pwd)" ||
  die "$worktree is not a worktree"
[ "$wt_common" = "$common" ] || die "$worktree belongs to another repository ($wt_common)"
[ -z "$(git -C "$worktree" status --porcelain)" ] || die "the train worktree $worktree is dirty"
if [ -n "$resume_source_candidate" ]; then
  [ "$(git -C "$worktree" rev-parse HEAD)" = "$resume_source_candidate" ] ||
    die "source resume worktree HEAD differs from the named candidate"
fi

base_tool() {
  # base_tool <base> <subcommand> [args...]: the verifier committed at <base>,
  # with the result parser it ships, run directly with "$SOUNDNESS_PYTHON3" -I. An anchor
  # that carries no verifier (the bootstrap) is refused (status 2): the
  # candidate never judges itself.
  local at="$1" dir rc
  shift
  if ! git -C "$repo" cat-file -e "${at}:scripts/soundness_attestation.py" 2>/dev/null; then
    say "UNANCHORED: ${at} carries no scripts/soundness_attestation.py; no landed verifier can judge the candidate"
    return 2
  fi
  dir="$(mktemp -d "${TMPDIR:-/tmp}/land-main-verifier.XXXXXX")" || return 2
  mkdir "$dir/scripts"
  git -C "$repo" show "${at}:scripts/soundness_attestation.py" >"$dir/scripts/soundness_attestation.py" || {
    rm -rf "$dir"; return 2; }
  git -C "$repo" show "${at}:scripts/matrix_results.py" >"$dir/scripts/matrix_results.py" 2>/dev/null ||
    rm -f "$dir/scripts/matrix_results.py"
  "$SOUNDNESS_PYTHON3" -I "$dir/scripts/soundness_attestation.py" "$@"
  rc=$?
  rm -rf "$dir"
  return "$rc"
}

anchored_verify() {
  # anchored_verify <commit> <anchor>: the LANDING verdict of the verifier
  # committed at <anchor> on <commit> (0 attested for landing; see
  # scripts/soundness_attestation.py for the other statuses).
  local commit="$1" at="$2"
  say "anchored: the verifier committed at ${at} judges ${commit} (landing verdict)"
  base_tool "$at" verify "$commit" --repo "$worktree" --landing --anchor "$at"
}

landing_scope_args() {
  # landing_scope_args <base>: "--scope portable" when the base's verifier
  # defers the x86-64-native class and this host cannot run it (not native
  # x86-64, no SOUNDNESS_X86_HOST); nothing (a full run) otherwise.
  local at="$1"
  [ -z "${SOUNDNESS_X86_HOST:-}" ] || return 0
  ! base_tool "$at" host --require-native-x86_64 >/dev/null 2>&1 || return 0
  if base_tool "$at" deferred-classes 2>/dev/null | grep -q '"x86_64-native"'; then
    printf '%s\n' --scope portable
  fi
}

candidate_preflights() {
  local commit="$1" at="$2" check
  if ! git -C "$repo" cat-file -e "${at}:scripts/soundness_attestation.py" 2>/dev/null; then
    say "UNANCHORED: the remote main ${at} carries no scripts/soundness_attestation.py"
    die "no landed verifier exists; nothing was attested or pushed"
  fi
  [ -f "$worktree/scripts/check_path_case_collisions.py" ] ||
    die "path-collision pre-flight missing; nothing was attested or pushed"
  say "pre-flight: tracked paths of ${commit}"
  "$SOUNDNESS_PYTHON3" -I -B "$worktree/scripts/check_path_case_collisions.py" \
    --root "$worktree" --rev "$commit" ||
    die "path-collision pre-flight failed; nothing was attested or pushed"
  for check in check_fmt check_tippy; do
    [ -x "$worktree/scripts/${check}.sh" ] ||
      die "${check} pre-flight missing; nothing was attested or pushed"
    say "pre-flight: scripts/${check}.sh"
    (CDPATH= cd -- "$worktree" && "./scripts/${check}.sh") ||
      die "${check} pre-flight failed; nothing was attested or pushed"
  done
  [ "$(git -C "$worktree" rev-parse HEAD)" = "$commit" ] &&
    [ -z "$(git -C "$worktree" status --porcelain)" ] ||
    die "candidate changed during pre-flights; nothing was attested or pushed"
}

candidate_source_checks() {
  local commit="$1" check
  [ -f "$worktree/scripts/check_path_case_collisions.py" ] ||
    die "source tracked-path check missing; nothing was pushed"
  "$SOUNDNESS_PYTHON3" -I -B "$worktree/scripts/check_path_case_collisions.py" \
    --root "$worktree" --rev "$commit" ||
    die "source tracked-path check failed; nothing was pushed"
  for check in "${source_checks[@]}"; do
    say "source qualification: $check"
    # Replace the argument parser: preserve ordinary inherited descriptors
    # and let the train retain/reap the actual check, without a second launcher.
    "$SOUNDNESS_PYTHON3" -I -c \
      'import os, shlex, sys; args = shlex.split(sys.argv[1]); os.chdir(sys.argv[2]); os.execvp(args[0], args)' \
      "$check" "$worktree" || die "focused source check failed; nothing was pushed"
    [ "$(git -C "$worktree" rev-parse HEAD)" = "$commit" ] &&
      [ -z "$(git -C "$worktree" status --porcelain)" ] ||
      die "candidate changed during focused checks; nothing was pushed"
  done
}

attempt=1
transport="$repo/scripts/github_transport.py"
while :; do
  say "attempt ${attempt}/${attempts}: fetching ${remote}/main"
  base="$("$SOUNDNESS_PYTHON3" -I "$transport" --repo "$repo" --remote "$remote" main)" || die "cannot fetch ${remote}/main"
  if [ -n "$resume_source_candidate" ]; then
    [ "$(git -C "$worktree" rev-parse HEAD)" = "$resume_source_candidate" ] &&
      [ -z "$(git -C "$worktree" status --porcelain)" ] ||
      die "source resume candidate changed before qualification"
    git -C "$worktree" merge-base --is-ancestor "$base" "$resume_source_candidate" ||
      die "remote main advanced beyond the source resume candidate; preserved it for ordinary merging and qualification"
    for index in "${!lanes[@]}"; do
      git -C "$worktree" merge-base --is-ancestor "${lane_commits[$index]}" "$resume_source_candidate" ||
        die "lane ${lanes[$index]} is not an ancestor of the source resume candidate"
    done
    candidate="$resume_source_candidate"
    say "resuming existing development source ${candidate}; no checkout or recreation; NOT ATTESTED"
  else
  git -C "$worktree" -c advice.detachedHead=false checkout --quiet --detach "$base" || die "cannot check out $base"
  for index in "${!lanes[@]}"; do
    lane="${lanes[$index]}"
    if git -C "$worktree" merge-base --is-ancestor "${lane_commits[$index]}" HEAD; then
      say "lane $lane is already in the batch base"
      continue
    fi
    if ! git -C "$worktree" merge --quiet --no-ff --no-edit \
         -m "Merge ${lane} into main (landing train)" "${lane_commits[$index]}"; then
      git -C "$worktree" merge --abort 2>/dev/null || :
      die "lane $lane does not merge onto ${base}; nothing was pushed"
    fi
  done
  candidate="$(git -C "$worktree" rev-parse HEAD)"
  fi
  if [ -z "$resume_source_candidate" ] && [ "$candidate" = "$base" ]; then
    say "nothing to land: every lane is already in ${remote}/main ${base}"
    exit 0
  fi
  if [ "$source_only" -eq 1 ]; then
    candidate_source_checks "$candidate"
    if [ "$push" -eq 0 ]; then
      say "source-checked ${candidate}; --no-push: not landing it; NOT ATTESTED"
      exit 0
    fi
    push_rc=0
    "$SOUNDNESS_PYTHON3" -I "$transport" --repo "$worktree" --remote "$remote" source-land "$candidate" --base "$base" || push_rc=$?
    if [ "$push_rc" -eq 0 ]; then
      say "landed development source ${candidate} on ${remote}/main; NOT ATTESTED"
      exit 0
    fi
  else
  candidate_preflights "$candidate" "$base"
  scope_args=()
  while IFS= read -r word; do
    [ -z "$word" ] || scope_args+=("$word")
  done < <(landing_scope_args "$base")
  say "candidate ${candidate} (base ${base}); running scripts/soundness_check.sh --attest ${scope_args[*]+"${scope_args[*]}"}"
  if ! (CDPATH= cd -- "$worktree" && ./scripts/soundness_check.sh --attest ${scope_args[@]+"${scope_args[@]}"}); then
    die "the soundness gate failed for ${candidate}; nothing was pushed"
  fi
  if ! anchored_verify "$candidate" "$base"; then
    die "${candidate} does not verify against its base ${base}; nothing was pushed"
  fi
  if [ "$push" -eq 0 ]; then
    say "attested ${candidate}; --no-push: not landing it"
    exit 0
  fi
  [ -x "$worktree/hooks/pre-push" ] || die "mandatory hooks/pre-push is missing or not executable"
  if ! (CDPATH= cd -- "$worktree" && printf '%s %s %s %s\n' HEAD "$candidate" refs/heads/main "$base" |
      ./hooks/pre-push "$remote"); then
    die "mandatory pre-push checks refused ${candidate}; nothing was pushed"
  fi
  push_rc=0
  "$SOUNDNESS_PYTHON3" -I "$transport" --repo "$worktree" --remote "$remote" land "$candidate" --base "$base" || push_rc=$?
  if [ "$push_rc" -eq 0 ]; then
    say "landed ${candidate} on ${remote}/main with its attestation records"
    exit 0
  fi
  fi
  [ "$push_rc" -ne 75 ] || die "unacknowledged atomic write: retained transport receipt requires reconciliation; no retry"
  moved="$("$SOUNDNESS_PYTHON3" -I "$transport" --repo "$repo" --remote "$remote" main)" ||
    die "publication failed (transport exit ${push_rc}); ${remote}/main readback unavailable, ref state unknown; candidate preserved; see the transport diagnostic and any retained receipt above"
  if [ "$moved" = "$base" ]; then
    die "publication of ${candidate} failed (transport exit ${push_rc}); readback confirms ${remote}/main unchanged at ${base}; candidate preserved; see the transport diagnostic and any retained receipt above"
  fi
  if [ -n "$resume_source_candidate" ]; then
    die "remote main moved during source resume (base ${base}, observed ${moved}; transport exit ${push_rc}); candidate preserved for fresh ordinary merging and qualification; see the transport diagnostic and any retained receipt above"
  fi
  if [ "$attempt" -ge "$attempts" ]; then
    die "${remote}/main moved again (${moved}); retry budget of ${attempts} exhausted, nothing landed"
  fi
  say "${remote}/main moved to ${moved} while the gate ran; re-merging on it"
  attempt=$((attempt + 1))
done
