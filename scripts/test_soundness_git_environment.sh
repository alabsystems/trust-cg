#!/usr/bin/env bash
# Actual local pre-push context around the production repository-query helpers.
# No compiler, remote network, or soundness attestation is run by this fixture.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
repo_fixture="$(mktemp -d "${TMPDIR:-/tmp}/soundness_git_environment.XXXXXX")"
trap 'rm -rf "$repo_fixture"' EXIT HUP INT TERM

# Extract the real cleanup invocation and HEAD/status checks. The attestation
# record check is the real scripts/soundness_attestation.py, run inside the hook.
# The fixture has no alternative production mode which can bypass the gate.
awk '
  /^isolate_git_repository_environment\(\)/ { active=1 }
  /^# Gate runners\./ { active=0 }
  active { print }
' "$repo_root/scripts/soundness_check.sh" >"$repo_fixture/queries.sh"
grep -Fxq 'isolate_git_repository_environment || exit 1' "$repo_fixture/queries.sh"
source "$repo_fixture/queries.sh"
fixture_git="$(command -v git)"

# Do not inherit signing, hooks, or arbitrary fixture-affecting user policy.
# This explicit non-repository config must survive the production scrub.
export GIT_CONFIG_GLOBAL="$repo_fixture/user.conf" GIT_CONFIG_NOSYSTEM=1
cat >"$GIT_CONFIG_GLOBAL" <<'EOF'
[user]
    name = Soundness hook fixture
    email = soundness-hook@example.invalid
[commit]
    gpgSign = false
[test]
    preserved = global-user-config
EOF

fixture_cg="$repo_fixture/cg"
fixture_clean="$repo_fixture/clean sibling"
fixture_ay="$repo_fixture/ay sibling"
for fixture_repo in "$fixture_cg" "$fixture_clean" "$fixture_ay"; do
  git init -q "$fixture_repo"
  printf '%s\n' "$fixture_repo" >"$fixture_repo/source"
  git -C "$fixture_repo" add source
  git -C "$fixture_repo" commit -qm initial
done
fixture_c1="$(git -C "$fixture_cg" rev-parse HEAD)"
fixture_clean_head="$(git -C "$fixture_clean" rev-parse HEAD)"
fixture_ay_head="$(git -C "$fixture_ay" rev-parse HEAD)"
[ "$fixture_c1" != "$fixture_clean_head" ]
[ "$fixture_clean_head" != "$fixture_ay_head" ]
# Attestation records live in the CLEAN sibling, so a query that obeyed the
# hook's GIT_DIR (the trust-cg fixture) would not find them: one whose subject
# tree is the subject's, one whose recorded tree is wrong.
fixture_tool="$repo_root/scripts/soundness_attestation.py"
make_record() {
  local ref="$1" tree="$2" dir="$repo_fixture/record-$1"
  mkdir -p "$dir"
  printf '{"schema": "trust-cg-soundness-attestation-v1", "subject": {"commit": "%s", "tree": "%s"}, "scope": "full", "host": {"triple": "fixture-host"}, "legs": []}\n' \
    "$fixture_clean_head" "$tree" >"$dir/attestation.json"
  local blob tree_id oid
  blob="$(git -C "$fixture_clean" hash-object -w "$dir/attestation.json")"
  tree_id="$(printf '100644 blob %s\tattestation.json\n' "$blob" | git -C "$fixture_clean" mktree)"
  oid="$(git -C "$fixture_clean" commit-tree "$tree_id" -p "$fixture_clean_head" -m "fixture record $ref")"
  git -C "$fixture_clean" update-ref "refs/attest/soundness/$fixture_clean_head/$ref" "$oid"
  printf '%s\n' "$oid"
}
fixture_record="$(make_record fixture-host "$(git -C "$fixture_clean" rev-parse "HEAD^{tree}")")"
fixture_bad_tree="$(make_record bad-tree "$(git -C "$fixture_cg" rev-parse "HEAD^{tree}")")"
git init -q --bare "$repo_fixture/remote.git"

export SOUNDNESS_FIXTURE_ROOT="$repo_fixture" SOUNDNESS_FIXTURE_GIT="$fixture_git"
export SOUNDNESS_FIXTURE_CG="$fixture_cg" SOUNDNESS_FIXTURE_CLEAN="$fixture_clean"
export SOUNDNESS_FIXTURE_AY="$fixture_ay" SOUNDNESS_FIXTURE_TOOL="$fixture_tool"
export SOUNDNESS_FIXTURE_C1="$fixture_c1" SOUNDNESS_FIXTURE_CLEAN_HEAD="$fixture_clean_head"
export SOUNDNESS_FIXTURE_AY_HEAD="$fixture_ay_head" SOUNDNESS_FIXTURE_RECORD="$fixture_record"
export SOUNDNESS_FIXTURE_BAD_TREE="$fixture_bad_tree"

cat >"$fixture_cg/.git/hooks/pre-push" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[ -n "${GIT_DIR:-}" ] || { echo 'fixture did not receive hook GIT_DIR'; exit 90; }
printf 'actual pre-push fixture entered\n'
# Add other real repository-local overrides after Git has located this hook.
export GIT_WORK_TREE="$SOUNDNESS_FIXTURE_CG"
export GIT_COMMON_DIR="$SOUNDNESS_FIXTURE_CG/.git"
export GIT_INDEX_FILE="$SOUNDNESS_FIXTURE_CG/.git/index"
export GIT_OBJECT_DIRECTORY="$SOUNDNESS_FIXTURE_CG/.git/objects"
export GIT_TEST_FUTURE_LOCAL=must-be-cleared

# Pin the original failure: raw `git -C` observes the wrong repository here.
raw_head="$("$SOUNDNESS_FIXTURE_GIT" -C "$SOUNDNESS_FIXTURE_CLEAN" rev-parse HEAD)"
[ "$raw_head" = "$SOUNDNESS_FIXTURE_C1" ] || exit 91

# Real repository operations are used except for explicit failure injections.
# The future local name tests that isolation follows Git's inventory, rather
# than a fixed subset.
git() {
  if [ "${1:-}" = rev-parse ] && [ "${2:-}" = --local-env-vars ]; then
    case "$SOUNDNESS_FIXTURE_FAULT" in
      inventory-error) return 74 ;;
      inventory-empty) return 0 ;;
      inventory-malformed) printf 'HOME\n'; return 0 ;;
    esac
    "$SOUNDNESS_FIXTURE_GIT" "$@" || return $?
    printf 'GIT_TEST_FUTURE_LOCAL\n'
    return 0
  fi
  if [ "${1:-}" = -C ] && [ "${2:-}" = "$SOUNDNESS_FIXTURE_CLEAN" ]; then
    if [ "$SOUNDNESS_FIXTURE_FAULT" = head-error ] && [ "${3:-}" = rev-parse ]; then
      printf '%s\n' "$SOUNDNESS_FIXTURE_CLEAN_HEAD"
      return 74
    fi
    if [ "$SOUNDNESS_FIXTURE_FAULT" = status-error ] && [ "${3:-}" = status ]; then
      return 74
    fi
  fi
  "$SOUNDNESS_FIXTURE_GIT" "$@"
}
record() { printf '%s %s %s\n' "$2" "$1" "$3"; }
source "$SOUNDNESS_FIXTURE_ROOT/queries.sh"
[ -z "${GIT_DIR+x}${GIT_WORK_TREE+x}${GIT_COMMON_DIR+x}${GIT_INDEX_FILE+x}${GIT_OBJECT_DIRECTORY+x}${GIT_TEST_FUTURE_LOCAL+x}" ] || exit 92
[ "$(git config --get test.preserved)" = global-user-config ] || exit 93
[ "$GIT_CONFIG_GLOBAL" = "$SOUNDNESS_FIXTURE_ROOT/user.conf" ] || exit 94
[ "$GIT_CONFIG_NOSYSTEM" = 1 ] || exit 95

for fixture_kind in CG CLEAN AY; do
  case "$fixture_kind" in
    CG) fixture_dir="$SOUNDNESS_FIXTURE_CG"; fixture_head="$SOUNDNESS_FIXTURE_C1" ;;
    CLEAN) fixture_dir="$SOUNDNESS_FIXTURE_CLEAN"; fixture_head="$SOUNDNESS_FIXTURE_CLEAN_HEAD" ;;
    AY) fixture_dir="$SOUNDNESS_FIXTURE_AY"; fixture_head="$SOUNDNESS_FIXTURE_AY_HEAD" ;;
  esac
  # This is the same helper used by BOTH the real preflight and post-run phase.
  check_repo_worktree_clean "hook: $fixture_kind worktree clean" "$fixture_dir" || exit 1
  [ "$(repo_head "$fixture_dir")" = "$fixture_head" ] || exit 96
done
# The attestation tool, started from this hook environment (GIT_DIR and the
# overrides above still exported to it: the shell function scrub does not reach
# a child process started before it), must read the repository it is given.
record_check() {
  env GIT_DIR="$SOUNDNESS_FIXTURE_CG/.git" GIT_WORK_TREE="$SOUNDNESS_FIXTURE_CG" \
    GIT_OBJECT_DIRECTORY="$SOUNDNESS_FIXTURE_CG/.git/objects" \
    python3 "$SOUNDNESS_FIXTURE_TOOL" check-record --repo "$SOUNDNESS_FIXTURE_CLEAN" \
    --commit "$SOUNDNESS_FIXTURE_CLEAN_HEAD" --record "$1" --triple "$2"
}
if ! record_check "$SOUNDNESS_FIXTURE_RECORD" fixture-host; then
  echo 'FAIL actual attestation record query'
  exit 1
fi
if [ "$SOUNDNESS_FIXTURE_FAULT" = record-tree-mismatch ]; then
  record_check "$SOUNDNESS_FIXTURE_BAD_TREE" bad-tree || { echo 'FAIL record subject tree refused'; exit 1; }
fi
if [ "$SOUNDNESS_FIXTURE_FAULT" = record-wrong-host ]; then
  record_check "$SOUNDNESS_FIXTURE_RECORD" another-host || { echo 'FAIL record host refused'; exit 1; }
fi

# A failure appearing only after an initially successful check cannot borrow
# the earlier clean observation (the production post-run path uses this too).
if [ "$SOUNDNESS_FIXTURE_FAULT" = late-status-error ]; then
  SOUNDNESS_FIXTURE_FAULT=status-error
  check_repo_worktree_clean 'post-run: CLEAN worktree clean' "$SOUNDNESS_FIXTURE_CLEAN" || exit 1
fi
printf 'GIT_HOOK_FIXTURE_PASSED\n'
EOF
chmod +x "$fixture_cg/.git/hooks/pre-push"

fixture_pass=0
fixture_fail=0
run_hook_case() {
  local name="$1" expected="$2" diagnostic="$3" output rc=0
  export SOUNDNESS_FIXTURE_FAULT="$name"
  output="$(GIT_DIR="$fixture_cg/.git" \
    "$fixture_git" -C "$fixture_cg" -c core.hooksPath="$fixture_cg/.git/hooks" \
    push --quiet "$repo_fixture/remote.git" "HEAD:refs/heads/$name" 2>&1)" || rc=$?
  if printf '%s\n' "$output" | grep -Fq 'actual pre-push fixture entered' && \
     printf '%s\n' "$output" | grep -Fq "$diagnostic" && \
     { { [ "$expected" = pass ] && [ "$rc" -eq 0 ]; } || \
       { [ "$expected" = fail ] && [ "$rc" -ne 0 ] && \
         ! printf '%s\n' "$output" | grep -Fq 'GIT_HOOK_FIXTURE_PASSED'; }; }; then
    printf 'ok - actual hook Git environment: %s\n' "$name"
    fixture_pass=$((fixture_pass + 1))
  else
    printf 'not ok - actual hook Git environment: %s (rc=%s, output: %s)\n' "$name" "$rc" "$output" >&2
    fixture_fail=$((fixture_fail + 1))
  fi
}

run_hook_case clean pass GIT_HOOK_FIXTURE_PASSED
printf 'dirty\n' >>"$fixture_clean/source"
run_hook_case dirty-clean fail 'FAIL hook: CLEAN worktree clean uncommitted files present'
printf '%s\n' "$fixture_clean" >"$fixture_clean/source"
printf 'untracked\n' >"$fixture_ay/untracked"
run_hook_case dirty-ay fail 'FAIL hook: AY worktree clean uncommitted files present'
rm "$fixture_ay/untracked"
run_hook_case inventory-error fail 'cannot enumerate Git repository-local environment'
run_hook_case inventory-empty fail 'cannot enumerate Git repository-local environment'
run_hook_case inventory-malformed fail 'invalid Git repository-local environment name'
run_hook_case head-error fail 'cannot read committed HEAD'
run_hook_case status-error fail 'cannot query worktree status'
run_hook_case late-status-error fail 'FAIL post-run: CLEAN worktree clean cannot query worktree status'
run_hook_case record-tree-mismatch fail 'FAIL record subject tree refused'
run_hook_case record-wrong-host fail 'FAIL record host refused'

printf '%d hook environment cases passed, %d failed\n' "$fixture_pass" "$fixture_fail"
[ "$fixture_fail" -eq 0 ]
