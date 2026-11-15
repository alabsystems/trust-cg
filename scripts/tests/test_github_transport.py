"""Real local objects plus bounded native-agh protocol negatives; no network writes."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import github_transport as transport


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="cg-transport-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.repo, self.remote = self.root / "repo", self.root / "remote.git"
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                   GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@example.invalid")
        self.environment = patch.dict(os.environ, env, clear=True)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        transport.run(["git", "init", "-q", self.repo])
        transport.run(["git", "init", "-q", "--bare", self.remote])
        self.git("config", "user.name", "t")
        self.git("config", "user.email", "t@example.invalid")
        (self.repo / "source").write_text("base\n")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD")
        self.git("remote", "add", "origin", str(self.remote))
        self.git("push", "-q", "origin", "HEAD:refs/heads/main")
        self.local = transport.Transport(self.repo)

    def git(self, *args):
        return transport.git(self.repo, *args)

    def record(self, subject=None, host="fixture"):
        subject = subject or self.base
        tree = self.git("rev-parse", f"{subject}^{{tree}}")
        oid = transport.run(["git", "-C", self.repo, "commit-tree", tree, "-p", subject], input=f"record {host}\n").stdout.strip()
        name = f"{transport.RECORDS}{subject}/{host}"
        self.git("update-ref", name, oid)
        return name, oid

    def github(self):
        self.git("config", "remote.origin.url", "https://github.com/example/cg.git")
        return transport.Transport(self.repo)

    def test_remote_binding_refuses_other_hosts_credentials_and_ambiguous_urls(self):
        for bad in ("git@elsewhere.invalid:example/cg.git", "ssh://git@elsewhere.invalid/example/cg",
                    "https://user:secret@github.com/example/cg.git", "https://github.com/example/cg?x=1",
                    "https://github.com/../cg", "ext::evil"):
            with self.subTest(remote=bad):
                self.git("config", "remote.origin.url", bad)
                with self.assertRaises(transport.Refused) as error:
                    transport.Transport(self.repo)
                self.assertNotIn("secret", str(error.exception))
        self.git("config", "remote.origin.url", "https://github.com/example/cg.git")
        self.git("config", "--add", "remote.origin.url", "https://github.com/example/other.git")
        with self.assertRaises(transport.Refused):
            transport.Transport(self.repo)

    def test_same_repository_pushurl_is_bound_but_other_repository_refuses(self):
        self.github()
        self.git("config", "remote.origin.pushurl", "git@github.com:example/cg.git")
        self.assertEqual(transport.Transport(self.repo).slug, "example/cg")
        self.git("config", "remote.origin.pushurl", "git@github.com:example/other.git")
        with self.assertRaises(transport.Refused):
            transport.Transport(self.repo)

    def test_local_main_and_pin_fetch_real_objects_without_tracking_pin_drift(self):
        self.assertEqual(self.local.fetch_main("origin"), self.base)
        (self.repo / "source").write_text("next\n")
        self.git("commit", "-qam", "next")
        next_commit = self.git("rev-parse", "HEAD")
        self.git("push", "-q", "origin", "HEAD:refs/heads/main")
        clone = self.root / "empty"
        transport.run(["git", "init", "-q", clone])
        empty = transport.Transport(clone, str(self.remote))
        empty.pin(self.base)
        self.assertEqual(transport.git(clone, "cat-file", "-t", self.base), "commit")
        self.assertNotEqual(self.base, next_commit)
        self.assertEqual(transport.git(clone, "for-each-ref", "refs/heads/"), "")

    def test_record_import_keeps_malformed_subject_presence_and_never_prunes(self):
        name, oid = self.record()
        malformed = transport.RECORDS + "not-a-subject/host"
        self.git("update-ref", malformed, oid)
        self.git("push", "-q", "origin", f"{name}:{name}", f"{malformed}:{malformed}")
        self.git("update-ref", "-d", malformed)
        self.assertEqual(self.local.records(), 2)
        self.assertEqual(self.git("rev-parse", malformed), oid)
        transport.git(self.remote, "update-ref", "-d", malformed)
        self.assertEqual(self.local.records(), 1)
        self.assertEqual(self.git("rev-parse", malformed), oid)

    def test_changed_record_refuses_atomic_import_and_preserves_local_evidence(self):
        name, original = self.record()
        _, replacement = self.record(host="other")
        transport.git(self.remote, "fetch", "-q", self.repo, replacement)
        transport.git(self.remote, "update-ref", name, replacement)
        with self.assertRaisesRegex(transport.Refused, "immutable"):
            self.local.records()
        self.assertEqual(self.git("rev-parse", name), original)

    def test_failed_expected_oid_never_imports_a_record(self):
        name, oid = self.record()
        self.git("push", "-q", "origin", f"{name}:{name}")
        self.git("update-ref", "-d", name)
        with patch.object(self.local, "refs", return_value={name: self.base}):
            with self.assertRaisesRegex(transport.Refused, "admitted raw"):
                self.local.records()
        self.assertEqual(self.git("for-each-ref", name), "")

    def test_bad_catalogs_refuse_before_any_object_fetch(self):
        native = self.github()
        good = dict(ref=transport.RECORDS + self.base + "/host", object=dict(sha=self.base))
        for body in ({}, [good, good], [dict(ref="refs/heads/main", object=dict(sha=self.base))],
                     [dict(ref=good["ref"], object=dict(sha="0" * 40))], [dict(ref=good["ref"], object=None)]):
            with self.subTest(body=body), patch.object(native, "api", return_value=body), \
                    patch.object(native, "fetch") as fetch:
                with self.assertRaises(transport.Refused):
                    native.records()
                fetch.assert_not_called()

    def test_catalog_link_and_failed_response_cannot_silently_truncate(self):
        native = self.github()
        for response in (dict(status=200, headers={"Link": '<next>; rel="next"'}, body=[]),
                         dict(status=401, headers={}, body=[]), dict(status=200, body=[])):
            with patch.object(transport, "run", return_value=subprocess.CompletedProcess([], 0, json.dumps(response), "")):
                with self.assertRaises(transport.Refused):
                    native.api("git/matching-refs/attest/soundness/")

    def test_native_fetch_retains_original_source_admission_and_pins_every_oid(self):
        native = self.github()
        calls = []
        actual = transport.run

        def agh(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            self.assertEqual(Path(argv[4]), self.repo)
            if argv[2] == "check-local":
                return subprocess.CompletedProcess(argv, 0, "{}", "")
            self.assertEqual(argv[:4], ["agh", "repo", "fetch", "example/cg"])
            rows = json.loads(Path(argv[-1]).read_text())
            self.assertEqual(rows[0]["expected_oid"], self.base)
            self.git("update-ref", rows[0]["into"], self.base)
            return subprocess.CompletedProcess(argv, 0, "{}", "")

        with patch.object(transport, "run", side_effect=agh):
            native.pin(self.base)
        self.assertEqual(len(calls), 2)
        with patch.object(transport, "run", side_effect=transport.Refused("original source refused")):
            with self.assertRaisesRegex(transport.Refused, "original source refused"):
                native.pin(self.base)

    def test_real_atomic_local_push_leases_main_and_records_together(self):
        (self.repo / "source").write_text("candidate\n")
        self.git("commit", "-qam", "candidate")
        candidate = self.git("rev-parse", "HEAD")
        name, oid = self.record(candidate)
        self.local.push(candidate, base=self.base)
        self.assertEqual(transport.git(self.remote, "rev-parse", "refs/heads/main"), candidate)
        self.assertEqual(transport.git(self.remote, "rev-parse", name), oid)
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/updates.json"))
        self.assertEqual(len(receipts), 1)
        rows = json.loads(receipts[0].read_text())
        self.assertEqual({row["ref"] for row in rows}, {name, "refs/heads/main"})
        self.assertEqual(next(row for row in rows if row["ref"] == "refs/heads/main")["before"], self.base)

    def test_source_publication_moves_only_main_and_keeps_attested_default_strict(self):
        (self.repo / "source").write_text("source candidate\n")
        self.git("commit", "-qam", "source candidate")
        candidate = self.git("rev-parse", "HEAD")
        with self.assertRaisesRegex(transport.Refused, "no local attestation"):
            self.local.push(candidate, base=self.base)
        self.record(candidate)  # Even a local record must not travel in source mode.
        self.local.push(candidate, base=self.base, source_only=True)
        self.assertEqual(transport.git(self.remote, "rev-parse", "refs/heads/main"), candidate)
        self.assertEqual(transport.git(self.remote, "for-each-ref", transport.RECORDS), "")
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/updates.json"))
        self.assertEqual(len(receipts), 1)
        self.assertEqual(json.loads(receipts[0].read_text()),
                         [dict(ref="refs/heads/main", before=self.base, after=candidate)])

    def test_source_publication_requires_base_and_refuses_non_fast_forward(self):
        tree = self.git("rev-parse", "HEAD^{tree}")
        unrelated = transport.run(["git", "-C", self.repo, "commit-tree", tree], input="unrelated\n").stdout.strip()
        with self.assertRaisesRegex(transport.Refused, "exact main base"):
            self.local.push(unrelated, source_only=True)
        with self.assertRaises(transport.Refused):
            self.local.push(unrelated, base=self.base, source_only=True)
        self.assertEqual(transport.git(self.remote, "rev-parse", "refs/heads/main"), self.base)
        self.assertFalse((self.repo / ".git/github-transport-receipts").exists())

    def test_cached_graft_cannot_turn_unrelated_source_publication_into_fast_forward(self):
        tree = self.git("rev-parse", "HEAD^{tree}")
        unrelated = transport.run(["git", "-C", self.repo, "commit-tree", tree], input="unrelated graft candidate\n").stdout.strip()
        info = self.repo / ".git/info"
        info.mkdir(exist_ok=True)
        (info / "grafts").write_text(unrelated + " " + self.base + "\n")
        # Demonstrate the actual unsafe Git view, even with replacement refs
        # disabled. Both commits are genuine independent roots.
        raw_env = dict(os.environ)
        raw_env.pop("GIT_GRAFT_FILE", None)
        raw_env["GIT_NO_REPLACE_OBJECTS"] = "1"
        raw = subprocess.run(["git", "-C", str(self.repo), "merge-base", "--is-ancestor", self.base, unrelated],
                             env=raw_env, capture_output=True)
        self.assertEqual(raw.returncode, 0)
        with self.assertRaises(transport.Refused):
            self.local.push(unrelated, base=self.base, source_only=True)
        self.assertEqual(transport.git(self.remote, "rev-parse", "refs/heads/main"), self.base)
        self.assertFalse((self.repo / ".git/github-transport-receipts").exists())

    def test_unknown_source_write_retains_main_readback_and_never_retries(self):
        (self.repo / "source").write_text("source candidate\n")
        self.git("commit", "-qam", "source candidate")
        candidate = self.git("rev-parse", "HEAD")
        native = self.github()
        actual, calls = transport.run, []

        def agh(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            return subprocess.CompletedProcess(argv, 0 if argv[2] == "check-local" or "--dry-run" in argv else 75,
                                               "lost acknowledgement", "")

        with patch.object(native, "refs", return_value={}), patch.object(native, "main", return_value=self.base), \
                patch.object(transport, "run", side_effect=agh):
            with self.assertRaisesRegex(transport.Unknown, "reconcile"):
                native.push(candidate, base=self.base, source_only=True)
        self.assertEqual(len(calls), 3)
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/readback.json"))
        self.assertEqual(len(receipts), 1)
        self.assertEqual(json.loads(receipts[0].read_text()), {"refs/heads/main": self.base})

    def test_unknown_native_write_retains_receipt_readback_and_is_not_retried(self):
        native = self.github()
        self.record()
        actual, calls = transport.run, []

        def agh(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            self.assertEqual(Path(argv[4]), self.repo, "screen the original source")
            if argv[2] == "check-local":
                return subprocess.CompletedProcess(argv, 0, "{}", "")
            return subprocess.CompletedProcess(argv, 0 if "--dry-run" in argv else 75, "lost acknowledgement", "")

        with patch.object(native, "refs", return_value={}), patch.object(transport, "run", side_effect=agh):
            with self.assertRaisesRegex(transport.Unknown, "reconcile"):
                native.push(self.base)
        self.assertEqual(len(calls), 3)
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/readback.json"))
        self.assertEqual(len(receipts), 1)
        self.assertTrue((receipts[0].parent / "write.stdout").exists())

    def test_native_preflight_refusal_never_invokes_write(self):
        native = self.github()
        self.record()
        actual, calls = transport.run, []
        reason = "agh: could_not_run exit=3 side_effect=none why=\"git push exited 128: fatal: did not receive expected object 5d3010\"\n"
        outcome = '{"outcome":"not_sent","dry_run":true}\n'

        def agh(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            return subprocess.CompletedProcess(argv, 0 if argv[2] == "check-local" else 3,
                                               outcome, reason)

        with patch.object(native, "refs", return_value={}), patch.object(transport, "run", side_effect=agh):
            with self.assertRaisesRegex(transport.Refused, "preflight.*exit 3; write not invoked.*retained receipt"):
                native.push(self.base)
        self.assertEqual(len(calls), 2)
        self.assertIn("--dry-run", calls[-1])
        self.assertEqual(list((self.repo / ".git/github-transport-receipts").glob("*/write.stdout")), [])
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/dry-run.json"))
        self.assertEqual(len(receipts), 1)
        self.assertEqual(json.loads(receipts[0].read_text()), {"exit": 3})
        self.assertEqual((receipts[0].parent / "dry-run.stderr").read_text(), reason)
        self.assertEqual((receipts[0].parent / "dry-run.stdout").read_text(), outcome)

    def test_dangling_symbolic_record_never_creates_its_unrelated_target(self):
        name, oid = self.record()
        self.git("push", "-q", "origin", f"{name}:{name}")
        self.git("update-ref", "-d", name)
        self.git("symbolic-ref", name, "refs/heads/unrelated")
        with self.assertRaisesRegex(transport.Refused, "symbolic"):
            self.local.records()
        self.assertEqual(self.git("symbolic-ref", name), "refs/heads/unrelated")
        self.assertEqual(self.git("for-each-ref", "refs/heads/unrelated"), "")

    def test_symlink_ref_parent_and_hardlinked_reflog_refuse_before_import(self):
        name, oid = self.record()
        self.git("push", "-q", "origin", f"{name}:{name}")
        self.git("update-ref", "-d", name)
        outside = self.root / "outside"
        outside.mkdir()
        parent = self.repo / ".git" / transport.RECORDS.rstrip("/") / self.base
        if parent.exists():
            parent.rmdir()
        parent.parent.mkdir(parents=True, exist_ok=True)
        parent.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(transport.Refused, "symlink"):
            self.local.records()
        self.assertEqual(list(outside.iterdir()), [])
        parent.unlink()
        parent.mkdir()
        log = self.repo / ".git/logs" / name
        log.parent.mkdir(parents=True, exist_ok=True)
        if log.exists():
            log.unlink()
        marker = self.root / "unrelated.log"
        marker.write_text("unchanged\n")
        os.link(marker, log)
        with self.assertRaisesRegex(transport.Refused, "unaliased"):
            self.local.records()
        self.assertEqual(marker.read_text(), "unchanged\n")
        self.assertFalse((parent / "fixture").exists())

    def test_tracking_symbolic_destination_and_concurrent_import_refuse(self):
        tracking = "refs/remotes/origin/main"
        self.git("symbolic-ref", tracking, "refs/heads/unrelated")
        with self.assertRaisesRegex(transport.Refused, "symbolic"):
            self.local.fetch_main("origin")
        self.git("update-ref", "--no-deref", "-d", tracking)
        (self.repo / "source").write_text("concurrent\n")
        self.git("commit", "-qam", "concurrent")
        replacement = self.git("rev-parse", "HEAD")
        actual = self.local.fetch

        def fetch(snapshot):
            actual(snapshot)
            self.git("update-ref", tracking, replacement)

        with patch.object(self.local, "fetch", side_effect=fetch):
            with self.assertRaises(transport.Refused):
                self.local.fetch_main("origin")
        self.assertEqual(self.git("rev-parse", tracking), replacement)

    def test_direct_import_ignores_all_inherited_git_repository_and_config_context(self):
        other = self.root / "other"
        transport.run(["git", "init", "-q", other])
        fake = self.root / "config"
        fake.write_text('[remote "origin"]\nurl = ext::evil\n')
        poison = dict(GIT_DIR=str(other / ".git"), GIT_CONFIG_GLOBAL=str(fake), GIT_CONFIG_COUNT="1",
                      GIT_CONFIG_KEY_0="remote.origin.url", GIT_CONFIG_VALUE_0="ext::evil",
                      GIT_OBJECT_DIRECTORY=str(other / ".git/objects"), GIT_GRAFT_FILE=str(fake))
        with patch.dict(os.environ, poison):
            raw = subprocess.run(["git", "-C", self.repo, "config", "--get", "remote.origin.url"],
                                 capture_output=True, text=True)
            self.assertEqual(raw.stdout.strip(), "ext::evil", "poison control actually affects raw Git")
            direct = transport.Transport(self.repo)
            self.assertEqual(direct.local, self.remote)
            self.assertEqual(direct.fetch_main("origin"), self.base)

    def test_native_main_cache_rejects_dangling_symbolic_ref_before_refresh(self):
        native = self.github()
        self.git("symbolic-ref", "refs/agh/fetched-main", "refs/heads/unrelated")
        actual, calls = transport.run, []

        def admitted(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            self.assertEqual(argv[2], "check-local", "symbolic cache must refuse before native refresh")
            return subprocess.CompletedProcess(argv, 0, "{}", "")

        with patch.object(transport, "run", side_effect=admitted):
            with self.assertRaisesRegex(transport.Refused, "symbolic"):
                native.fetch_main("origin")
        self.assertEqual(len(calls), 1)
        self.assertEqual(self.git("for-each-ref", "refs/heads/unrelated"), "")

    def test_native_main_fetches_the_exact_checkout_using_original_objects_only_as_data(self):
        native = self.github()
        before = self.git("rev-parse", "HEAD"), (self.repo / "source").read_bytes()
        actual, calls = transport.run, []

        def agh(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            if argv[2] == "check-local":
                self.assertEqual(Path(argv[4]), self.repo)
            else:
                self.assertEqual(list(map(str, argv)), ["agh", "repo", "fetch", "example/cg",
                    str(self.repo), "--ref", self.base, "--into", "refs/agh/fetched-main",
                    "--checkout-closure", "--checkout-cache", str(self.repo)])
                self.git("update-ref", "refs/agh/fetched-main", self.base)
            return subprocess.CompletedProcess(argv, 0, "{}", "")

        with patch.object(native, "main", return_value=self.base) as resolve, \
                patch.object(transport, "run", side_effect=agh):
            self.assertEqual(native.fetch_main("origin"), self.base)
        resolve.assert_called_once_with()
        self.assertEqual(len(calls), 2)
        self.assertEqual(self.git("rev-parse", "refs/remotes/origin/main"), self.base)
        self.assertEqual((self.git("rev-parse", "HEAD"), (self.repo / "source").read_bytes()), before)

    def test_native_main_stale_checkout_or_refusal_cannot_import_or_fall_back(self):
        native = self.github()
        tracking = "refs/remotes/origin/main"
        self.git("update-ref", tracking, self.base)
        (self.repo / "source").write_text("new main\n")
        self.git("commit", "-qam", "new main")
        new_main = self.git("rev-parse", "HEAD")
        actual = transport.run
        for rejected in (False, True):
            calls = []

            def agh(argv, **kwargs):
                if argv[0] != "agh":
                    return actual(argv, **kwargs)
                calls.append(list(map(str, argv)))
                if argv[2] != "check-local":
                    self.assertEqual(argv[2], "fetch")
                    self.assertEqual(argv[argv.index("--ref") + 1], new_main)
                    if rejected:
                        raise transport.Refused("native checkout refused")
                    self.git("update-ref", "refs/agh/fetched-main", self.base)
                return subprocess.CompletedProcess(argv, 0, "{}", "")

            with self.subTest(native_refused=rejected), \
                    patch.object(native, "main", return_value=new_main), \
                    patch.object(transport, "run", side_effect=agh):
                with self.assertRaises(transport.Refused):
                    native.fetch_main("origin")
            self.assertEqual(self.git("rev-parse", tracking), self.base)
            self.assertEqual(len(calls), 2, "no legacy fetch or admission fallback")

    def test_native_main_source_admission_failure_precedes_remote_resolution(self):
        native = self.github()
        actual, calls = transport.run, []

        def reject(argv, **kwargs):
            if argv[0] != "agh":
                return actual(argv, **kwargs)
            calls.append(list(map(str, argv)))
            self.assertEqual(list(map(str, argv)),
                ["agh", "repo", "check-local", "example/cg", str(self.repo)])
            raise transport.Refused("original source refused")

        with patch.object(native, "main") as resolve, \
                patch.object(transport, "run", side_effect=reject):
            with self.assertRaisesRegex(transport.Refused, "original source refused"):
                native.fetch_main("origin")
        resolve.assert_not_called()
        self.assertEqual(len(calls), 1)


if __name__ == "__main__":
    unittest.main()
