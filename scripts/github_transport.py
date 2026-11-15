#!/usr/bin/env python3
"""Exact GitHub transport through native agh; local paths remain fixture transport.

This module transports objects and refs, never gives an attestation verdict.
Record imports are additive: a missing remote ref must not erase local evidence
that ended the landing exception. Native agh disables hooks. The attested train
runs the mandatory pre-push gate before ``land``; ordinary ``source-land``
transports only main after focused checks and creates no attestation records.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlsplit
import uuid

RECORDS = "refs/attest/soundness/"
ZERO = "0" * 40
OID = re.compile(r"[0-9a-f]{40}\Z")
GITHUB = re.compile(r"(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
                    r"([A-Za-z0-9][A-Za-z0-9_.-]*)/([A-Za-z0-9][A-Za-z0-9_.-]*?)(?:\.git)?/?\Z")


class Refused(Exception):
    pass


class Unknown(Refused):
    """A write was invoked without a successful acknowledgement; never retry."""


def run(argv, *, input=None, check=True):
    # One child environment for CLI and direct imports. Never inherit a Git
    # repository/config/object graft or replacement view from a hook/caller.
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_ATTR_NOSYSTEM="1",
               GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull, GIT_OPTIONAL_LOCKS="0",
               GIT_TERMINAL_PROMPT="0", GIT_ALLOW_PROTOCOL="file")
    argv = list(map(str, argv))
    if argv[0] == "git":
        argv[1:1] = ["-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false"]
    result = subprocess.run(argv, input=input, env=env, capture_output=True, text=True, timeout=300)
    if check and result.returncode:
        # Do not echo configured URLs or command output: either can contain credentials.
        raise Refused(f"{Path(str(argv[0])).name} operation failed (exit {result.returncode})")
    return result


def git(repo, *args, **kwargs):
    return run(["git", "-C", repo, *args], **kwargs).stdout.strip()


def sha(value):
    if not isinstance(value, str) or not OID.fullmatch(value) or value == ZERO:
        raise Refused("expected a nonzero raw object ID")
    return value


def ref(repo, name):
    if not isinstance(name, str) or not name.startswith("refs/"):
        raise Refused("expected a full ref name")
    git(repo, "check-ref-format", name)
    return name


def common_dir(repo):
    return Path(git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))


def guard_ref(repo, name):
    """Physical custody as at native agh's cache boundary; caller owns source.

    --no-deref protects Git symbolic refs, not filesystem aliases or the
    append-only reflog. Recheck immediately before the CAS transaction too.
    """
    ref(repo, name)
    common = common_dir(repo)
    for relative in (name, "logs/" + name, "packed-refs"):
        current = common
        parts = relative.split("/")
        for index, component in enumerate(parts):
            current = current / component
            try:
                metadata = current.lstat()
            except FileNotFoundError:
                break
            if stat.S_ISLNK(metadata.st_mode):
                raise Refused("local ref or reflog traverses a filesystem symlink")
            if index < len(parts) - 1:
                if not stat.S_ISDIR(metadata.st_mode):
                    raise Refused("local ref or reflog parent is not a directory")
            elif not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
                raise Refused("local ref or reflog is not an unaliased regular file")
            elif relative == name:
                with current.open("rb") as stream:
                    if stream.read(4) == b"ref:":
                        raise Refused("local destination is a symbolic ref")


def old_ref(repo, name):
    guard_ref(repo, name)
    value = git(repo, "rev-parse", "--verify", name, check=False)
    return sha(value) if value else ZERO


def import_refs(repo, values, before):
    updates = ["start"]
    for name, oid in sorted(values.items()):
        guard_ref(repo, name)
        updates.append(f"update {name} {sha(oid)} {before[name]}")
    updates.extend(["prepare", "commit", ""])
    if values:
        run(["git", "-C", repo, "update-ref", "--no-deref", "--stdin"], input="\n".join(updates))


def github_slug(url):
    match = GITHUB.fullmatch(url)
    if match is None or any(part in {".", ".."} for part in match.groups()):
        raise Refused("remote is not a canonical credential-free github.com repository URL")
    return "/".join(match.groups())


class Transport:
    def __init__(self, repo, remote="origin"):
        self.repo = Path(repo).resolve()
        # Read the configured bytes, not `remote get-url` (which applies insteadOf).
        configured = run(["git", "-C", self.repo, "config", "--get-all", f"remote.{remote}.url"], check=False)
        values = configured.stdout.splitlines()
        if configured.returncode not in (0, 1) or len(values) > 1:
            raise Refused("remote must name exactly one configured repository")
        url = values[0] if values else remote
        if not url or any(ord(c) < 32 for c in url):
            raise Refused("invalid remote location")
        self.slug = None
        self.local = None
        if GITHUB.fullmatch(url):
            self.slug = github_slug(url)
        else:
            parsed = urlsplit(url)
            if parsed.scheme == "file" and not parsed.netloc and not parsed.query and not parsed.fragment:
                path = Path(unquote(parsed.path))
            elif not parsed.scheme and ":" not in url and not url.startswith("-"):
                path = Path(url)
                if not path.is_absolute():
                    path = self.repo / path
            else:
                raise Refused("remote must be canonical GitHub or a local repository path")
            if not path.is_dir():
                raise Refused("local repository path is unavailable")
            self.local = path.resolve()
        pushurls = run(["git", "-C", self.repo, "config", "--get-all", f"remote.{remote}.pushurl"], check=False)
        if pushurls.returncode not in (0, 1):
            raise Refused("cannot inspect push repository")
        for pushurl in pushurls.stdout.splitlines():
            if self.slug is None or github_slug(pushurl).lower() != self.slug.lower():
                raise Refused("push URL must name the same GitHub repository")

    def api(self, suffix):
        result = run(["agh", "api", f"repos/{self.slug}/{suffix}", "--include"])
        try:
            response = json.loads(result.stdout)
        except ValueError as error:
            raise Refused("agh returned invalid JSON") from error
        if not isinstance(response, dict) or response.get("status") != 200:
            raise Refused("GitHub ref read did not return HTTP 200")
        headers = response.get("headers")
        if (not isinstance(headers, dict)
                or any(not isinstance(k, str) or not isinstance(v, str) or (k.lower() == "link" and v)
                       for k, v in headers.items())):
            # The matching-refs API has no pagination parameters. A future or
            # unexpected Link must refuse, never silently truncate the catalog.
            raise Refused("unexpected pagination or missing headers in GitHub ref catalog")
        return response.get("body")

    def refs(self, prefix):
        ref(self.repo, prefix.rstrip("/"))
        if self.local is not None:
            output = git(self.local, "for-each-ref", "--format=%(refname) %(objectname)", prefix)
            rows = [dict(ref=name, object=dict(sha=oid)) for name, oid in
                    (line.split(" ", 1) for line in output.splitlines())]
        else:
            if prefix.endswith("/"):
                rows = self.api("git/matching-refs/" + prefix.removeprefix("refs/"))
            else:
                rows = [self.api("git/ref/" + prefix.removeprefix("refs/"))]
        if not isinstance(rows, list) or len(rows) > 100000:
            raise Refused("invalid or oversized GitHub ref catalog")
        found = {}
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("object"), dict):
                raise Refused("malformed ref catalog row")
            name, oid = ref(self.repo, row.get("ref")), sha(row["object"].get("sha"))
            if (not name.startswith(prefix) or (not prefix.endswith("/") and name != prefix)
                    or name in found):
                raise Refused("duplicate or out-of-scope ref catalog row")
            found[name] = oid
        return found

    def main(self):
        rows = self.refs("refs/heads/main")
        if set(rows) != {"refs/heads/main"}:
            raise Refused("main ref catalog is missing or ambiguous")
        return rows["refs/heads/main"]

    def fetch(self, sources):
        """Fetch a complete admitted snapshot to unique private refs, then import."""
        if self.slug is not None:
            run(["agh", "repo", "check-local", self.slug, self.repo])
        nonce = uuid.uuid4().hex
        rows = [dict(source=name, into=f"refs/agh/trust-cg/{nonce}/{i}", expected_oid=oid)
                for i, (name, oid) in enumerate(sorted(sources.items()))]
        with tempfile.TemporaryDirectory(prefix="trust-cg-fetch-") as temporary:
            for start in range(0, len(rows), 2048):
                batch = rows[start:start + 2048]
                if self.local is not None:
                    run(["git", "-C", self.repo, "-c", "protocol.allow=never", "-c", "protocol.file.allow=always",
                         "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--no-recurse-submodules",
                         self.local, *(f"{row['source']}:{row['into']}" for row in batch)])
                else:
                    path = Path(temporary) / "batch.json"
                    path.write_text(json.dumps(batch))
                    # Native agh judges the original repository; do not clone
                    # away a source-admission refusal or rewrite its config.
                    run(["agh", "repo", "fetch", self.slug, self.repo, "--input", path])
        for row in rows:
            if git(self.repo, "rev-parse", "--verify", row["into"]) != row["expected_oid"]:
                raise Refused("fetched ref differs from its admitted raw object ID")
        return rows

    def fetch_main(self, remote):
        destination = ref(self.repo, f"refs/remotes/{remote}/main")
        # Capture before any network work, so a concurrent import cannot be
        # overwritten by a later observation from this invocation.
        before = old_ref(self.repo, destination)
        if self.slug is None:
            oid = self.main()
            self.fetch({"refs/heads/main": oid})
        else:
            run(["agh", "repo", "check-local", self.slug, self.repo])
            cache = "refs/agh/fetched-main"
            guard_ref(self.repo, cache)
            # Resolve the fresh remote identity before requesting its complete
            # checkout and ancestry metadata. Local objects are cache DATA,
            # checked by native agh; neither their refs nor artifacts grant
            # authority. Historical checkout bodies are not a main-source input.
            expected = self.main()
            run(["agh", "repo", "fetch", self.slug, self.repo,
                 "--ref", expected, "--into", cache, "--checkout-closure",
                 "--checkout-cache", self.repo])
            guard_ref(self.repo, cache)
            oid = sha(git(self.repo, "rev-parse", "--verify", cache))
            if oid != expected:
                raise Refused("native main checkout differs from the fresh remote identity")
        if git(self.repo, "cat-file", "-t", oid) != "commit":
            raise Refused("main must directly name a commit")
        import_refs(self.repo, {destination: oid}, {destination: before})
        return oid

    def records(self, subject=None):
        prefix = RECORDS + (sha(subject) + "/" if subject else "")
        snapshot = self.refs(prefix)
        before = {name: old_ref(self.repo, name) for name in snapshot}
        if any(before[name] not in (ZERO, oid) for name, oid in snapshot.items()):
            raise Refused("remote changed an existing immutable local attestation record")
        self.fetch(snapshot)
        # All expected objects were checked before the atomic local import.
        # No prune: malformed or absent remote records cannot revive an exception.
        import_refs(self.repo, snapshot, before)
        return len(snapshot)

    def pin(self, oid):
        self.fetch({sha(oid): oid})
        if git(self.repo, "cat-file", "-t", oid) != "commit":
            raise Refused("dependency pin must directly name a commit")

    def push(self, subject, *, base=None, source_only=False):
        subject = sha(subject)
        if source_only and base is None:
            raise Refused("source publication requires an exact main base")
        if self.slug is not None:
            run(["agh", "repo", "check-local", self.slug, self.repo])
        prefix = RECORDS + subject + "/"
        local = "" if source_only else git(self.repo, "for-each-ref", "--format=%(refname) %(objectname)", prefix)
        records = dict(line.split(" ", 1) for line in local.splitlines())
        if not source_only and not records:
            raise Refused("candidate has no local attestation records")
        remote = {} if source_only else self.refs(prefix)
        if set(remote) - set(records):
            raise Refused("remote has candidate records absent from the local verified set")
        updates = []
        for name, oid in sorted(records.items()):
            ref(self.repo, name)
            sha(oid)
            before = remote.get(name, ZERO)
            if before != ZERO and before != oid:
                raise Refused("existing attestation record is immutable")
            if before != oid:
                updates.append(dict(ref=name, before=before, after=oid))
        if base is not None:
            if self.main() != sha(base):
                raise Refused("main moved before the atomic push was prepared")
            git(self.repo, "merge-base", "--is-ancestor", base, subject)
            if base != subject:
                updates.append(dict(ref="refs/heads/main", before=base, after=subject))
        if not updates:
            return
        if len(updates) > 128:
            raise Refused("atomic push exceeds native agh's 128-ref bound")
        common = Path(git(self.repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))
        directory = common / "github-transport-receipts" / uuid.uuid4().hex
        directory.mkdir(parents=True, mode=0o700)
        path = directory / "updates.json"
        path.write_text(json.dumps(updates, indent=2) + "\n")
        if self.local is not None:
            argv = ["git", "-C", str(self.repo), "-c", "protocol.allow=never", "-c", "protocol.file.allow=always",
                    "-c", "core.hooksPath=/dev/null", "push", "--atomic", "--no-follow-tags", "--recurse-submodules=no",
                    *(f"--force-with-lease={row['ref']}:{row['before'] if row['before'] != ZERO else ''}" for row in updates)]
            suffix = [str(self.local), *(f"{row['after']}:{row['ref']}" for row in updates)]
            dry, actual = argv + ["--dry-run"] + suffix, argv + suffix
        else:
            if git(self.repo, "rev-parse", "--is-shallow-repository") != "false":
                raise Refused("atomic publication requires a complete source repository")
            actual = ["agh", "repo", "push", self.slug, str(self.repo), "--input", str(path)]
            dry = actual + ["--dry-run"]
        for phase, argv in (("dry-run", dry), ("write", actual)):
            try:
                result = run(argv, check=False)
            except (OSError, subprocess.SubprocessError) as error:
                (directory / f"{phase}.error").write_text(type(error).__name__ + "\n")
                if phase == "write":
                    raise Unknown(f"unacknowledged write; retained receipt {directory}; reconcile agh intent before retry") from error
                raise
            (directory / f"{phase}.stdout").write_text(result.stdout)
            (directory / f"{phase}.stderr").write_text(result.stderr)
            (directory / f"{phase}.json").write_text(json.dumps(dict(exit=result.returncode)) + "\n")
            if result.returncode:
                if phase == "write":
                    try:
                        readback = self.refs(prefix)
                        if base is not None:
                            readback["refs/heads/main"] = self.main()
                        (directory / "readback.json").write_text(json.dumps(readback, indent=2) + "\n")
                    except (Refused, OSError, subprocess.SubprocessError):
                        (directory / "readback.error").write_text("readback unavailable\n")
                    raise Unknown(f"write not acknowledged; retained receipt {directory}; reconcile agh intent before retry")
                raise Refused(f"atomic push preflight refused (exit {result.returncode}; write not invoked); "
                              f"retained receipt {directory}; reason in dry-run.stdout and dry-run.stderr")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--remote", default="origin")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("main")
    p = sub.add_parser("records")
    p.add_argument("--subject")
    p = sub.add_parser("pin")
    p.add_argument("oid")
    p = sub.add_parser("push-records")
    p.add_argument("subject")
    p = sub.add_parser("land")
    p.add_argument("subject")
    p.add_argument("--base", required=True)
    p = sub.add_parser("source-land")
    p.add_argument("subject")
    p.add_argument("--base", required=True)
    args = parser.parse_args()
    try:
        transport = Transport(args.repo, args.remote)
        if args.command == "main":
            print(transport.fetch_main(args.remote))
        elif args.command == "records":
            print(f"fetched {transport.records(args.subject)} record ref(s)")
        elif args.command == "pin":
            transport.pin(args.oid)
        else:
            transport.push(args.subject,
                           base=args.base if args.command in ("land", "source-land") else None,
                           source_only=args.command == "source-land")
        return 0
    except Unknown as error:
        print(f"github-transport: STOP: {error}", file=sys.stderr)
        return 75
    except (Refused, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"github-transport: refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
