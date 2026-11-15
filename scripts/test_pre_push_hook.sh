#!/usr/bin/env bash
# The real hooks/pre-push in a throwaway repository with a bare remote, a stub
# gate and a stub attestation tool. Nothing here reaches a network remote.
#
# The production tracked-path collision check is committed beside it: the hook
# runs it on every main push and blocks when it is missing.
#
# The stubs are committed into the fixture repository, because the hook runs
# the gate of the tree it pushes and the tool committed at the anchor: its
# verify answers 0 when a record ref exists for the commit (else 3), its
# landing-exception answers "in force" (0) unless HOOK_FIXTURE_EXCEPTION_ENDED=1
# (1), its deferred-classes defers x86_64-native when HOOK_FIXTURE_DEFER_X86=1,
# its host is never native x86-64, and the gate's --attest writes a record
# commit (single parent C) unless told to fail. The hook fetches and pushes
# records through the shared transport's local-bare fixture route.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
fixture="$(mktemp -d "${TMPDIR:-/tmp}/pre_push_hook.XXXXXX")"
trap 'rm -rf "$fixture"' EXIT HUP INT TERM
export GIT_CONFIG_GLOBAL="$fixture/user.conf" GIT_CONFIG_NOSYSTEM=1
cat >"$GIT_CONFIG_GLOBAL" <<'EOF'
[user]
    name = Pre-push hook fixture
    email = pre-push@example.invalid
[commit]
    gpgSign = false
[init]
    defaultBranch = main
EOF

work="$fixture/work"
remote="$fixture/remote.git"
export HOOK_FIXTURE_REMOTE_LOCATION="$remote"
git init -q --bare "$remote"
git init -q "$work"
mkdir -p "$work/hooks" "$work/scripts"
cp "$repo_root/hooks/pre-push" "$work/hooks/pre-push"
cp "$repo_root/scripts/check_path_case_collisions.py" "$work/scripts/check_path_case_collisions.py"
cp "$repo_root/scripts/github_transport.py" "$work/scripts/github_transport.py"
cat >"$work/scripts/soundness_attestation.py" <<'EOF'
import os, subprocess, sys
repo = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
with open(os.environ["HOOK_FIXTURE_LOG"], "a") as log:
    log.write("tool " + " ".join(sys.argv[1:]) + "\n")
command = sys.argv[1]
if command == "landing-exception":
    if "--help" in sys.argv[2:]:
        print("landing-exception --remote NAME" if os.environ.get("HOOK_FIXTURE_REMOTE_OPTION") == "1"
              else "landing-exception")
        sys.exit(0)
    if os.environ.get("HOOK_FIXTURE_DISCOVERY_UNKNOWN") == "1":
        print("UNDETERMINED: fixture discovery unavailable"); sys.exit(1)
    if os.environ.get("HOOK_FIXTURE_REMOTE_OPTION") == "1":
        expected = os.environ["HOOK_FIXTURE_REMOTE_LOCATION"]
        if "--remote" not in sys.argv or sys.argv[sys.argv.index("--remote") + 1] != expected:
            print("UNDETERMINED: wrong discovery remote"); sys.exit(2)
    if os.environ.get("HOOK_FIXTURE_EXCEPTION_ENDED") == "1":
        print("ENDED: fixture"); sys.exit(1)
    print("IN FORCE: fixture"); sys.exit(0)
if command == "deferred-classes":
    print('{"x86_64-native": "fixture"}' if os.environ.get("HOOK_FIXTURE_DEFER_X86") == "1" else "{}")
    sys.exit(0)
if command == "host":
    print("host triple: fixture; native x86-64: False"); sys.exit(1)
commit = sys.argv[2]
def git(*args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
sha = git("rev-parse", commit).stdout.strip()
if command == "fetch":
    sys.exit(0)
if command in ("verify", "verify-anchored"):
    refs = git("for-each-ref", f"refs/attest/soundness/{sha}/").stdout.strip()
    print(f"{sha}: attested (fixture)" if refs else f"{sha}: no record (fixture)")
    sys.exit(0 if refs else 3)
if command == "push":
    remote = sys.argv[sys.argv.index("--remote") + 1]
    spec = f"refs/attest/soundness/{sha}/*:refs/attest/soundness/{sha}/*"
    sys.exit(subprocess.run(["git", "-C", repo, "push", "--quiet", remote, spec]).returncode)
sys.exit(2)
EOF
cat >"$work/scripts/soundness_check.sh" <<'EOF'
#!/usr/bin/env bash
set -eu
echo "gate $*" >>"$HOOK_FIXTURE_LOG"
[ "$*" = --attest ] || [ "$*" = "--attest --scope portable" ] || exit 2
[ "${HOOK_FIXTURE_GATE_RC:-0}" -eq 0 ] || exit "$HOOK_FIXTURE_GATE_RC"
head="$(git rev-parse HEAD)"
tree="$(git mktree </dev/null)"
record="$(git commit-tree "$tree" -p "$head" -m 'fixture record')"
git update-ref "refs/attest/soundness/$head/fixture-host" "$record"
echo "wrote refs/attest/soundness/$head/fixture-host"
EOF
# The two pre-flight gates: each logs its call and answers HOOK_FIXTURE_FMT_RC /
# HOOK_FIXTURE_LINT_RC (default 0). They log to their own file so the cases that
# assert the attestation tool and gate were never called stay exact.
for pre in check_fmt check_tippy; do
  cat >"$work/scripts/$pre.sh" <<EOF
#!/usr/bin/env bash
echo "$pre" >>"\$HOOK_FIXTURE_PREFLIGHT_LOG"
case "$pre" in
  check_fmt) exit "\${HOOK_FIXTURE_FMT_RC:-0}" ;;
  *) exit "\${HOOK_FIXTURE_LINT_RC:-0}" ;;
esac
EOF
done
chmod +x "$work/hooks/pre-push" "$work/scripts/soundness_check.sh" \
  "$work/scripts/check_fmt.sh" "$work/scripts/check_tippy.sh"
git -C "$work" config core.hooksPath hooks
printf 'base\n' >"$work/source"
git -C "$work" add -A
git -C "$work" commit -qm base
git -C "$work" remote add origin "$remote"
# Seed the remote without the hook: the fixture's first main.
git -C "$work" push -q --no-verify origin HEAD:refs/heads/main

export HOOK_FIXTURE_LOG="$fixture/calls.log"
export HOOK_FIXTURE_PREFLIGHT_LOG="$fixture/preflight.log"
pass=0
failures=0
output=""
rc=0
push_main() {
  : >"$HOOK_FIXTURE_LOG"
  rc=0
  output="$(git -C "$work" push "${HOOK_FIXTURE_REMOTE_NAME:-origin}" "${1:-HEAD}:refs/heads/main" 2>&1)" || rc=$?
}
new_commit() {
  printf '%s\n' "$1" >>"$work/source"
  git -C "$work" commit -qam "$1"
}
check() {
  if eval "$2"; then
    printf 'ok - pre-push: %s\n' "$1"
    pass=$((pass + 1))
  else
    printf 'not ok - pre-push: %s (rc=%s, output: %s, calls: %s)\n' "$1" "$rc" "$output" \
      "$(tr '\n' ';' <"$HOOK_FIXTURE_LOG")" >&2
    failures=$((failures + 1))
  fi
}
remote_main() { git -C "$remote" rev-parse refs/heads/main; }

# No record: the gate runs, the records reach the remote, the push lands. The
# remote main it replaces (the seed) was never attested: the notice says so.
new_commit second
c="$(git -C "$work" rev-parse HEAD)"
push_main
check "unattested commit runs the gate, shares its records and lands" \
  '[ "$rc" -eq 0 ] && grep -qx "gate --attest" "$HOOK_FIXTURE_LOG" && [ "$(remote_main)" = "$c" ] &&
   git -C "$remote" rev-parse --verify -q "refs/attest/soundness/$c/fixture-host" >/dev/null'
check "an unattested predecessor is reported" \
  'printf "%s\n" "$output" | grep -q "NOTICE — the remote main being replaced"'
check "the candidate gets the anchor's landing verdict with the predecessor as anchor" \
  'grep -q "tool verify $c --repo .* --landing --anchor $(git -C "$work" rev-parse HEAD~1)" "$HOOK_FIXTURE_LOG" &&
   printf "%s\n" "$output" | grep -q "the verifier committed at $(git -C "$work" rev-parse HEAD~1) judges $c"'

# A record already present: the fast path, no gate, and the now-attested
# predecessor raises no notice.
new_commit third
c="$(git -C "$work" rev-parse HEAD)"
git -C "$work" update-ref "refs/attest/soundness/$c/fixture-host" \
  "$(git -C "$work" commit-tree "$(git -C "$work" mktree </dev/null)" -p "$c" -m record)"
push_main
check "an attested commit takes the fast path without running the gate" \
  '[ "$rc" -eq 0 ] && ! grep -q "^gate" "$HOOK_FIXTURE_LOG" && [ "$(remote_main)" = "$c" ] &&
   printf "%s\n" "$output" | grep -q "is attested"'
check "an attested predecessor raises no notice" \
  '! printf "%s\n" "$output" | grep -q "NOTICE"'

# A commit whose OWN verifier always answers "attested" cannot take the fast
# path: the verifier committed at the anchor (the remote main) judges it.
cat >"$work/scripts/soundness_attestation.py" <<'WEAK'
import sys
print("attested (a weakened verifier)")
sys.exit(0)
WEAK
git -C "$work" commit -qam "weaken the verifier"
before="$(remote_main)"
HOOK_FIXTURE_GATE_RC=1 push_main
check "a commit that weakens its own verifier does not attest itself" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] && grep -qx "gate --attest" "$HOOK_FIXTURE_LOG" &&
   ! printf "%s\n" "$output" | grep -q "a weakened verifier"'
git -C "$work" reset -q --hard HEAD~1

# C's own attestation tool runs nowhere in the hook: one that forges a record
# whenever it is invoked (fetch included) neither runs nor lands C.
cat >"$work/scripts/soundness_attestation.py" <<'FORGE'
import os, subprocess, sys
with open(os.environ["HOOK_FIXTURE_LOG"], "a") as log:
    log.write("C-tool " + " ".join(sys.argv[1:]) + "\n")
head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
tree = subprocess.run(["git", "mktree"], input="", capture_output=True, text=True).stdout.strip()
record = subprocess.run(["git", "commit-tree", tree, "-p", head, "-m", "forged"], capture_output=True,
                        text=True).stdout.strip()
subprocess.run(["git", "update-ref", f"refs/attest/soundness/{head}/forged", record])
print("attested (a forging tool)")
sys.exit(0)
FORGE
git -C "$work" commit -qam "a tool that forges records"
forger="$(git -C "$work" rev-parse HEAD)"
before="$(remote_main)"
HOOK_FIXTURE_GATE_RC=1 push_main
check "C's own attestation tool never runs in the hook, not even to fetch" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] && ! grep -q "^C-tool" "$HOOK_FIXTURE_LOG" &&
   [ -z "$(git -C "$work" for-each-ref "refs/attest/soundness/$forger/")" ]'
git -C "$work" reset -q --hard HEAD~1

# No landed predecessor anchors C: a forced push over a remote main this clone
# never fetched is blocked, even with a record for C in hand (the counterexample
# where C's own verifier judged C and the output called it "anchored").
other="$fixture/other"
git clone -q "$remote" "$other"
printf 'elsewhere\n' >>"$other/source"
git -C "$other" commit -qam elsewhere
git -C "$other" push -q --no-verify origin HEAD:refs/heads/main
elsewhere="$(git -C "$other" rev-parse HEAD)"
new_commit diverged
c="$(git -C "$work" rev-parse HEAD)"
git -C "$work" update-ref "refs/attest/soundness/$c/fixture-host" \
  "$(git -C "$work" commit-tree "$(git -C "$work" mktree </dev/null)" -p "$c" -m record)"
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(git -C "$work" push --force origin HEAD:refs/heads/main 2>&1)" || rc=$?
check "a forced push over a remote main this clone never fetched is blocked" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$elsewhere" ] && ! grep -q "^gate" "$HOOK_FIXTURE_LOG" &&
   ! grep -q "^tool verify $c" "$HOOK_FIXTURE_LOG" && printf "%s\n" "$output" | grep -q "unknown to this clone"'
git -C "$work" fetch -q origin main
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(git -C "$work" push --force origin HEAD:refs/heads/main 2>&1)" || rc=$?
check "a non-fast-forward push over a known remote main is blocked" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$elsewhere" ] && ! grep -q "^gate" "$HOOK_FIXTURE_LOG" &&
   printf "%s\n" "$output" | grep -q "is not an ancestor"'
git -C "$work" reset -q --hard "$elsewhere"

# A remote without main, and an anchor that predates the verifier (the
# bootstrap), have no landed verifier: blocked, never self-judged, and no
# bypass is advertised (no anchor's verifier said the exception is in force).
empty="$fixture/empty.git"
git init -q --bare "$empty"
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(git -C "$work" push "$empty" HEAD:refs/heads/main 2>&1)" || rc=$?
check "a first push of main is blocked" \
  '[ "$rc" -ne 0 ] && ! git -C "$empty" rev-parse -q --verify refs/heads/main >/dev/null &&
   printf "%s\n" "$output" | grep -q "first push of main" && [ ! -s "$HOOK_FIXTURE_LOG" ] &&
   ! printf "%s\n" "$output" | grep -q -- "--no-verify"'
bootstrap="$fixture/bootstrap.git"
git init -q --bare "$bootstrap"
git -C "$work" rm -q --cached scripts/soundness_attestation.py
git -C "$work" commit -qm "no verifier yet"
git -C "$work" push -q --no-verify "$bootstrap" HEAD:refs/heads/main
git -C "$work" add scripts/soundness_attestation.py
git -C "$work" commit -qm "the verifier arrives"
c="$(git -C "$work" rev-parse HEAD)"
git -C "$work" update-ref "refs/attest/soundness/$c/fixture-host" \
  "$(git -C "$work" commit-tree "$(git -C "$work" mktree </dev/null)" -p "$c" -m record)"
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(git -C "$work" push "$bootstrap" HEAD:refs/heads/main 2>&1)" || rc=$?
check "an anchor without a committed verifier (bootstrap) is blocked, not self-judged" \
  '[ "$rc" -ne 0 ] && [ "$(git -C "$bootstrap" rev-parse refs/heads/main)" = "$(git -C "$work" rev-parse HEAD~1)" ] &&
   printf "%s\n" "$output" | grep -q "UNANCHORED" && [ ! -s "$HOOK_FIXTURE_LOG" ]'
git -C "$work" reset -q --hard "$elsewhere"

# A failing gate blocks the push and names the interim exception once, while
# the anchor's verifier reports it in force.
new_commit fourth
before="$(remote_main)"
HOOK_FIXTURE_GATE_RC=1 push_main
check "a failing gate blocks the push" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] && printf "%s\n" "$output" | grep -q "soundness gate FAILED"'
check "--no-verify appears only as the labelled interim exception while it is in force" \
  '[ "$(printf "%s\n" "$output" | grep -c -- "--no-verify")" -eq 1 ] &&
   printf "%s\n" "$output" | grep -- "--no-verify" | grep -q "Interim exception (OD-LANDING-X86-DEFERRAL-20261008" &&
   grep -q "^tool landing-exception --repo .* --anchor $before" "$HOOK_FIXTURE_LOG"'
check "the 2026-09-27 exception is no longer advertised" \
  '! printf "%s\n" "$output" | grep -q "2026-09-27"'
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_EXCEPTION_ENDED=1 push_main
check "once the anchor's verifier reports the exception ended, --no-verify is never advertised" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] && ! printf "%s\n" "$output" | grep -q -- "--no-verify" &&
   printf "%s\n" "$output" | grep -q "interim exception has ENDED"'
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_DISCOVERY_UNKNOWN=1 push_main
check "unavailable discovery refuses bypass without claiming the exception ended" \
  '[ "$rc" -ne 0 ] && ! printf "%s\n" "$output" | grep -q -- "--no-verify" &&
   ! printf "%s\n" "$output" | grep -q "exception has ENDED" &&
   printf "%s\n" "$output" | grep -q "exception was not established"'
# Simulate a real transport disappearing AFTER main was advertised to Git.
# These invoke the real hook with a legacy anchor and actual failed local Git
# discovery, not a fake successful fetch or an invented attestation verdict.
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(cd "$work" && printf 'refs/heads/main %s refs/heads/main %s\n' \
  "$(git rev-parse HEAD)" "$before" | HOOK_FIXTURE_GATE_RC=1 \
  bash hooks/pre-push origin "$fixture/unavailable.git" 2>&1)" || rc=$?
check "a legacy local-only positive answer cannot survive actual failed discovery" \
  '[ "$rc" -ne 0 ] && ! printf "%s\n" "$output" | grep -q -- "--no-verify" &&
   printf "%s\n" "$output" | grep -q "complete attestation discovery failed"'
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(cd "$work" && printf 'refs/heads/main %s refs/heads/main %s\n' \
  "$(git rev-parse HEAD)" "$before" | HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_EXCEPTION_ENDED=1 \
  bash hooks/pre-push origin "$fixture/unavailable.git" 2>&1)" || rc=$?
check "a legacy retained ENDED answer remains conservative while discovery fails" \
  '[ "$rc" -ne 0 ] && ! printf "%s\n" "$output" | grep -q -- "--no-verify" &&
   printf "%s\n" "$output" | grep -q "exception has ENDED"'
stale_anchor="$(git -C "$work" rev-list --max-parents=0 HEAD)"
: >"$HOOK_FIXTURE_LOG"
rc=0
output="$(cd "$work" && printf 'refs/heads/main %s refs/heads/main %s\n' \
  "$(git rev-parse HEAD)" "$stale_anchor" | HOOK_FIXTURE_GATE_RC=1 \
  bash hooks/pre-push origin "$remote" 2>&1)" || rc=$?
check "a legacy local-only positive answer cannot use a stale advertised main" \
  '[ "$before" != "$stale_anchor" ] && [ "$rc" -ne 0 ] &&
   ! printf "%s\n" "$output" | grep -q -- "--no-verify" &&
   printf "%s\n" "$output" | grep -q "not the actual current main"'
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_REMOTE_OPTION=1 push_main
check "a discovery-capable anchor receives the actual origin push remote" \
  '[ "$rc" -ne 0 ] && grep -q "^tool landing-exception --repo .* --anchor .* --remote $remote$" "$HOOK_FIXTURE_LOG"'
git -C "$work" remote rename origin upstream
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_REMOTE_OPTION=1 HOOK_FIXTURE_REMOTE_NAME=upstream push_main
check "a nondefault push remote is not replaced by origin during discovery" \
  '[ "$rc" -ne 0 ] && grep -q "^tool landing-exception --repo .* --anchor .* --remote $remote$" "$HOOK_FIXTURE_LOG"'
git -C "$work" remote rename upstream origin
decoy="$fixture/decoy.git"
git clone -q --bare "$remote" "$decoy"
git -C "$work" remote set-url origin "$decoy"
git -C "$work" remote set-url --push origin "$remote"
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_REMOTE_OPTION=1 push_main
check "a decoy fetch URL cannot replace the actual push location" \
  '[ "$rc" -ne 0 ] && grep -q "^tool landing-exception --repo .* --anchor .* --remote $remote$" "$HOOK_FIXTURE_LOG"'
git -C "$work" remote set-url origin "$remote"
git -C "$work" config --unset-all remote.origin.pushurl
# The slow path runs the portable scope only when the anchor defers the
# x86-64-native class and this host has no x86-64 executor.
HOOK_FIXTURE_GATE_RC=1 push_main
check "without a deferral the slow path runs the full scope" \
  'grep -qx "gate --attest" "$HOOK_FIXTURE_LOG"'
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_DEFER_X86=1 push_main
check "a deferral by the anchor and no x86-64 executor run the portable scope" \
  'grep -qx "gate --attest --scope portable" "$HOOK_FIXTURE_LOG"'
HOOK_FIXTURE_GATE_RC=1 HOOK_FIXTURE_DEFER_X86=1 SOUNDNESS_X86_HOST=fixture-x86 push_main
check "an x86-64 executor keeps the full scope even under a deferral" \
  'grep -qx "gate --attest" "$HOOK_FIXTURE_LOG"'

# A red pre-flight gate blocks the push before the soundness gate runs.
new_commit lint-red
before="$(remote_main)"
HOOK_FIXTURE_LINT_RC=1 push_main
check "a red lint gate blocks the push" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] &&
   printf "%s\n" "$output" | grep -q "lint gate FAILED" && ! grep -q "^gate" "$HOOK_FIXTURE_LOG"'
HOOK_FIXTURE_FMT_RC=1 push_main
check "a red format gate blocks the push" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] &&
   printf "%s\n" "$output" | grep -q "format gate FAILED" && ! grep -q "^gate" "$HOOK_FIXTURE_LOG"'

# A pre-flight gate that is missing from the pushed tree blocks the push: the
# hook never skips a linter or formatter because its script moved.
for pre in check_tippy check_fmt; do
  git -C "$work" rm -q "scripts/$pre.sh"
  git -C "$work" commit -qm "no $pre"
  push_main
  check "a missing $pre gate blocks the push" \
    '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] &&
     printf "%s\n" "$output" | grep -q "gate missing" && ! grep -q "^gate" "$HOOK_FIXTURE_LOG"'
  git -C "$work" reset -q --hard HEAD~1
done
git -C "$work" rm -q scripts/check_path_case_collisions.py
git -C "$work" commit -qm "no case-collision check"
push_main
check "a missing case-collision check blocks the push" \
  '[ "$rc" -ne 0 ] && [ "$(remote_main)" = "$before" ] &&
   printf "%s\n" "$output" | grep -q "tracked-path collisions cannot be checked" &&
   ! grep -q "^gate" "$HOOK_FIXTURE_LOG"'
git -C "$work" reset -q --hard HEAD~1

# A non-main push is not gated.
push_branch_output="$(git -C "$work" push origin HEAD:refs/heads/topic 2>&1)" && push_branch_rc=0 || push_branch_rc=$?
: >"$HOOK_FIXTURE_LOG"
git -C "$work" push -q origin HEAD:refs/heads/topic2 2>/dev/null || :
check "a non-main push is not gated" \
  '[ "$push_branch_rc" -eq 0 ] && [ ! -s "$HOOK_FIXTURE_LOG" ]'

# A dirty worktree and a SHA that is not HEAD are blocked before any gate.
printf 'dirty\n' >>"$work/source"
push_main
check "a dirty worktree is blocked" \
  '[ "$rc" -ne 0 ] && printf "%s\n" "$output" | grep -q "worktree is dirty" && ! grep -q "^gate" "$HOOK_FIXTURE_LOG"'
git -C "$work" checkout -q -- source
new_commit fifth
push_main HEAD~1
check "a pushed SHA that is not HEAD is blocked" \
  '[ "$rc" -ne 0 ] && printf "%s\n" "$output" | grep -q "is not checked-out HEAD"'

# The hook never mentions --no-verify on a successful push.
push_main
check "a successful push does not advertise --no-verify" \
  '[ "$rc" -eq 0 ] && ! printf "%s\n" "$output" | grep -q -- "--no-verify"'

printf '%d pre-push hook cases passed, %d failed\n' "$pass" "$failures"
[ "$failures" -eq 0 ]
