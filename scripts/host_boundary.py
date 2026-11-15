#!/usr/bin/env python3
"""The host trust boundary of an attested soundness run (ruling LD-73).

    "$SOUNDNESS_PYTHON3" -I scripts/host_boundary.py --search-path "$PATH"
        --candidate DIR [--python3 FILE] [--git-repo DIR ...] [--tool FILE ...]
        [--tool-root FILE ...] [--cargo-root DIR ...]

X-HOST-P13 makes private what trust-cg and its gate scripts create, cache or
choose to execute: the AY private copy, the Clean/AY dependency checkouts and
their builds, the JIT caches, the solver memo and the private export of the
attested commit's proofs (scripts/private_cache.py holds them to the strict
rule: no group or other write bit at all). The user's own toolchain installs
(rustup/cargo, elan/lake, the Trust package), git and its configuration, and
the candidate checkout are the host's trust boundary instead: no tool can
defend a build against a user who can rewrite the compiler. This check makes
an --attest run FAIL CLOSED at that boundary. scripts/soundness_check.sh runs
it before it starts any other program (only the bash running it, the bash
that re-executed it, the python3 PATH finds, run with -I -S to print its
canonical path once in each of those two bash runs, and that pinned file,
which runs the environment scrub, the cache-base rule and this check, ran
earlier; each is judged here, the pinned file with --python3 as exactly the
interpreter running this check), and on a
refusal prints the FAIL with each path and the remedy, runs nothing else and
writes no attestation. This check does not judge the caller's
working directory, so an --attest run starts nothing there
(OD-XHOST-GATE-CWD-20261025): it works in / (root's, resolved through by
every judged path, no repository the gate uses) until this check has passed
and in the candidate checkout, judged here as a tree, from then on, and every
python3 the gate scripts start (inline `-c` and `-`, and script runs) runs
isolated with -I. Before the scrub it finds its own directory with bash
builtins, CDPATH ignored, and refuses one that does not hold the very script
bash runs, and it refuses a relative or empty PATH entry as this check does,
so the scrub's soundness_attestation.py is the candidate's and its python3
is found by absolute PATH entries only (repair round 2 of that ruling). It
runs only as bash reads it from the candidate's scripts/soundness_check.sh
file (refusing a run read from standard input or a -c string, or sourced),
and every python3 it and its helpers start is one interpreter, resolved
before the gate_env.sh prelude changes PATH, by its canonical path
(SOUNDNESS_PYTHON3; repair round 3). The legs start python3 by name on the
prelude's PATH, so this check refuses the run unless that lookup finds the
same interpreter with the same import path (repair round 4).

ANOTHER USER CAN WRITE an entry when it is owned by another account (its
owner can change it), except root and, for an entry in a root-owned
directory (a system package's file), a system account below UID_MIN
(/etc/login.defs; 500 on macOS), which no login user is (Ubuntu's
/usr/sbin/lldpcli is setuid _lldpd; each such entry is listed in the
report); or it is writable by every user (mode o+w); or it is
group-writable (g+w) and its group has a member other than this user; or a
POSIX access ACL lets another user or such a group write it; or, for a
directory, its POSIX DEFAULT ACL would let another user, such a group or
every user write an entry created in it (a default ACL overrides the umask,
so umask 077 cannot keep what the run creates there private; ruling LD-75).
A group's members are the names /etc/group (and the system's group
database, `grp`) lists for it plus every account /etc/passwd (and `pwd`)
gives it as primary group; a listed name with no account, a group with no
entry, and an account database that also comes from a source this check
cannot enumerate (an /etc/nsswitch.conf passwd or group source other than
files, compat or systemd, or a `+`/`-` compat line) all count as another
member. A
group-writable entry in a group with no other member (the user-private-group
scheme a umask 0002 relies on) is not writable by another user. Root is not
"another user": root-owned entries are accepted, as everywhere in X-HOST-P13.
SOUNDNESS_EXTRA_GROUP_FILE and SOUNDNESS_EXTRA_PASSWD_FILE each name one more
file in /etc's format whose entries are ADDED to those databases (a member, a
group or a uid mapping); they can only make a group count as shared, never
private (tests use them to stand in for a shared group): a gid only they name
stays a group with no entry, and a member only they give an account stays a
name with no account.

A directory a path is looked up IN may be writable by others when it has the
sticky bit and the entry looked up is this user's or root's (`/tmp`): nobody
else can rename or remove that entry. A directory whose ENTRIES are used (a
PATH directory, every directory of a judged tree) gets no such exemption:
another user could add a name to it.

WHAT IS JUDGED, every path resolved hop by hop as the kernel resolves it (every
directory looked up in, and every symlink's literal target, so no name on the
way can be re-pointed by another user afterwards). A path whose canonical
resolution enters /proc (procfs: /proc/self, /proc/thread-self, /proc/<pid>)
or /dev/fd (a symlink to /proc/self/fd on Linux, an fdescfs mount on macOS)
is refused outright: it names the CHECKING process's own view of the
filesystem, not the view the program that would use it has from its own
working directory (so GIT_SSH_COMMAND=/proc/self/cwd/tools/evil, judged in the
checker's directory, would run in git's work tree; finding (1) of the
X-HOST-P13 round-5 verifier, OD-XHOST-TRANSPORT-WORDS-20261024). /dev/null and
/dev/shm are below neither and keep passing:
* the account databases this rule reads (/etc/group, /etc/passwd,
  /etc/nsswitch.conf, /etc/login.defs, and the extra files);
* the interpreters already running: this python3 (and every existing
  absolute entry of its own `-I` import path, as a tree: the standard library
  and site directories and every directory their .pth files and
  sitecustomize put on it, as they ran when this check started; every
  python3 the gate scripts start, inline (`-c`, `-`) or a script, is this
  same interpreter and runs with -I, so it imports from that path and from
  nothing else -I would add: -I puts neither the working directory nor a
  script's own directory on sys.path, and a gate script that imports a
  sibling module inserts the judged candidate's scripts/ itself:
  OD-XHOST-GATE-CWD-20261025 and its repair rounds 2 and 3), --python3 (the
  gate's pinned interpreter, SOUNDNESS_PYTHON3: a canonical absolute path,
  judged with every directory it is looked up in and each pyvenv.cfg python3
  would read for it, and refused unless it is the file running this check,
  by canonical path and by device and inode; repair round 3; since python3
  derives its own executable name from argv[0], also refused when it is a
  `#!` script or, on Linux, when /proc/self/exe is another file; repair
  round 4) and each --tool (the gate's bash, and the programs it runs by
  absolute path: /usr/bin/env, the Cargo runner, and macOS's /usr/bin/arch
  and /usr/bin/true);
* the python3 a leg starts by name (judge_leg_python3, repair round 4): the
  first python3 on the PATH given (the prelude's), resolved hop by hop, must
  be the pinned file, by canonical path and by device and inode, and the
  pyvenv.cfg files python3 reads for the name it is found by (the directory
  of that name and its parent) must be the pinned file's or none, each
  judged as a path that no other user may create or change; so a leg's
  python3 is the interpreter whose import path is judged here, with that
  import path, and a wrapper, a copy, another installation or a virtual
  environment's python3 there refuses without running;
* what a python3 run WITHOUT -I (a leg's: the bridge tests start report
  scripts that way, by name: the interpreter above) adds to that path at
  startup: python3's user site-packages, as a tree (below), and every
  directory a path line of a .pth file there names, as a tree, read without
  running anything (judge_user_site); a .pth line python3 executes, a sitecustomize or
  usercustomize module in those directories, a .pth file that is not a
  regular file, holds a byte outside ASCII or holds a character
  str.splitlines splits a line at other than \\n and \\r (repair round 3)
  each refuse, since what that code puts on the path can be judged only by
  running it, or the lines python3 reads are not certainly the lines judged.
  The empty entry such a run puts first for `-c` and `-`, its working
  directory, is not judged: the gate gives no such run that entry, and a
  leg's working directory is the candidate checkout, a directory it names
  itself or one it creates (see NOT JUDGED);
* every PATH directory and every entry in it (the commands the run and the
  tools it starts find by name: git, python3, lake, rustup, cargo, targo,
  trustc, node, ssh, ...); a relative or empty PATH entry is refused;
* HOME and XDG_CONFIG_HOME themselves (nobody else may add a dotfile there);
* the locations CARGO_HOME, CARGO_TARGET_DIR, RUSTUP_HOME, ELAN_HOME,
  SOUNDNESS_DEPS_DIR and ATPKG_BIN name: a value that is set and not an
  absolute path (an empty one included) refuses, naming the variable, since
  Cargo, rustup, elan, gate_env.sh and private_cache.py resolve a relative
  one against their working directory, which this check does not judge (an
  empty one is refused as the simplest rule, not because it leads
  elsewhere); so does a tree
  root or --cargo-root that is not absolute (as a relative PATH entry; LD-75
  repair);
* TMPDIR (else /tmp), where the legs create their own entries: writable by
  others only with the sticky bit;
* as whole trees, symlinks out of them followed and their targets judged as
  trees too: CARGO_HOME (its proxies, and the registry and git sources whose
  build scripts the legs compile and run), RUSTUP_HOME, ELAN_HOME (the lake
  proxy and the Lean toolchains), the Trust package of the PATH trustc and
  targo, each --tool-root's install root (the island twin rustc), aterm's
  managed package prefix, CARGO_TARGET_DIR when set, python3's user
  site-packages (a python3 run without -I imports from it and reads its .pth
  files; above), node's legacy global module folders (~/.node_modules,
  ~/.node_libraries), on macOS ~/lib (scripts/trust_cargo.sh's
  DYLD_FALLBACK_LIBRARY_PATH), the candidate checkout
  (sources, scripts, configuration and its target/), the WORK TREE of each
  --git-repo (the Clean, AY and aterm sources, where git runs the preflight's
  `git fetch origin`, its lazy-fetch cat-files, `git worktree add`'s parent,
  the aterm commands and export_vt_tables, so what git's child finds there by
  a relative name, in that directory or below it, is judged where git
  resolves it; OD-XHOST-TRANSPORT-WORDS-20261024), and the git directories of
  the candidate and of each --git-repo (their config, hooks, info and object
  stores);
* git's own view of each repository the gate runs git in (repair round 3 of
  OD-XHOST-TRANSPORT-WORDS-20261024): for the candidate, each --git-repo,
  each Cargo git database ($CARGO_HOME/git/db/*) and checkout
  ($CARGO_HOME/git/checkouts/*/*), and each repository nested in the work
  tree of one of them (below), `git rev-parse` must
  report the directory itself as the work-tree top (a bare repository: as
  its git directory) and the git directories judged as trees. A core.worktree
  naming an ancestor or any other directory (git chdirs there and runs the
  fetch's uploadpack, transport and helpers from it), a subdirectory of a
  repository or a directory with no .git of its own (git searches the
  ancestors and uses that repository), a core.bare on a work tree's .git and
  a GIT_DIR naming another repository each refuse; so the work tree judged
  above is the directory git runs a configured program in.
  scripts/soundness_check.sh asks git the same of each pinned checkout before
  its first `git status` (a core.worktree in its config.worktree refuses);
* every object store such a git directory borrows objects from: each entry
  of its objects/info/alternates, followed through the alternates files of
  those stores in turn, judged as a whole tree. An alternates file this check
  cannot read or parse (a C-quoted line), an entry naming a missing store,
  and an objects/info/http-alternates file (stores named by URL) refuse. So
  does a GIT_OBJECT_DIRECTORY or GIT_ALTERNATE_OBJECT_DIRECTORIES in the
  environment (the gate's environment allowlist removes both; LD-75);
* Cargo's configuration search: Cargo merges .cargo/config.toml from its
  working directory and every ancestor. For the candidate checkout, each
  --cargo-root (the gate's SOUNDNESS_DEPS_DIR, where the Clean and AY
  checkouts are built), the user cache's trust-cg directory, CARGO_HOME and
  CARGO_TARGET_DIR, every canonical ancestor up to / in which another user
  can create an entry refuses, sticky or not (that user could create its
  .cargo after this check), unless it is sticky and already holds a .cargo
  directory of this user's or root's, which is then judged as a tree (a
  directory others can write without the sticky bit could have its .cargo
  renamed away, so it never passes). A checkout, cache or Cargo home below
  /tmp is therefore refused (LD-75). An ancestor whose default ACL lets
  another user write what is created in it refuses too, reported as that,
  whether or not it holds a .cargo;
* the configuration the run's git reads (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
  The set of git keys whose value names a program or a path git, a git
  helper (web--browse, difftool, mergetool, ...) or an extension runs is
  open, so an --attest run's git reads no system file
  (GIT_CONFIG_NOSYSTEM=1) and, as its global file, only the one this check
  writes on a pass (--gate-git-config, write_gate_git_config): the credential
  helpers, commit identity and core.excludesFile it judged from the user's
  system and global configuration (CARRIED_KEYS, CARRIED_CREDENTIAL_NAMES)
  and fetch.recurseSubmodules=false, read back with git. Every key of the
  local and worktree configuration of each repository the run uses git in
  must be on an allowlist of keys that name no program (LOCAL_DATA_KEYS,
  LOCAL_DATA_SECTION_KEYS, LOCAL_DATA_SECTIONS, and the judged
  LOCAL_JUDGED_PATH_KEYS), or the run refuses by name. Those repositories:
  the candidate, each --git-repo, each Cargo git database and checkout, each
  pinned checkout (scripts/soundness_check.sh runs --judge-git-config before
  its first `git status`), each local repository a remote location names,
  each submodule git directory below <git-dir>/modules (its config and
  config.worktree), and, recursively, every repository NESTED in the work
  tree of one of them (nested_repositories: every directory there holding a
  `.git`, and every gitlink path of the index holding one, a symlinked path
  included). git status descends into a populated submodule whatever its
  layout (a git directory absorbed below <git-dir>/modules, embedded in the
  path, or a `gitdir:` file naming any directory) and runs git there with
  that repository's own configuration (repair round 2). A nested repository
  is also judged as a tree with its git directories and their alternates,
  and git's view of it must give its own path as the work-tree top, so a
  core.worktree naming another directory refuses. Each kind of judgement of
  a repository (REPOSITORY_JUDGEMENTS: its configuration, its nested walk,
  as a nested repository, as a local remote) is made once per repository by
  directory identity, and one never stands in for another, so a repository
  that a local remote names AND git status enters is judged as both,
  whichever path reached it first (repair round 3: at 850f69fd0 a local
  remote's judgement made the nested one return early, so git's view of a
  populated submodule's work tree was never asked). A remote.*.uploadpack or
  .receivepack refuses outright in every scope (git passes a local remote's
  path to it as its last argument). A remote.*.url or .pushurl and a
  submodule.*.url naming a local path or file:// repository is judged as
  such a repository, and a relative, `~`, ext:: or non-plain file://
  location refuses. A local branch.<name>.remote, branch.<name>.pushRemote
  or remote.pushDefault naming neither `.` nor a remote whose url is
  configured there is judged as a location. A file in a git directory's
  remotes/ or branches/ (a remote defined outside the configuration)
  refuses;
* git's configuration as git reads it in each of those repositories: the
  user's system and global files `git var` names (or the defaults), and,
  whatever GIT_CONFIG_GLOBAL, GIT_CONFIG_SYSTEM and GIT_CONFIG_NOSYSTEM name,
  the default files Cargo's built-in libgit2 reads itself (/etc/gitconfig,
  the XDG git config, ~/.gitconfig, with their includes; the only programs
  Cargo runs from them are its credential helpers). This check's own git and
  libgit2 still read them, so a key the rules below refuse there refuses the
  run even though the run's git no longer reads it; the
  XDG attributes and ignore files, every file `git config
  --list --show-origin` reads for each repository (includes too), the
  directory core.hooksPath names, and every key that names a command
  (filters, fsmonitor, credential helpers, core.alternateRefsCommand,
  gpg.ssh.defaultKeyCommand, remote.<name>.uploadpack, alias.*, ...). Every
  such value is a shell command, except an alias.* value without a leading
  `!` (below); git strips exactly one leading `!` from an alias.* value and
  a credential helper, and none from any other key. The program, the first
  word (split where the shell splits words: spaces, tabs, newlines; not at
  U+00A0), is judged: an absolute or `~/` path resolved, a bare name found
  on PATH, a relative path with a slash and a `~`/`~user` word refused. The
  value is read by the TEXT of its words (OD-XHOST-TRANSPORT-WORDS-20261024),
  and refuses when: it holds a shell metacharacter; its first word is one
  the shell reads as reserved (`!`, `if`, `time`, `[[`, ...) or begins with
  `!` (`!! /x` is `! /x` to the shell, which runs /x; repair round 4); its
  first word holds `=` (an environment assignment, `PATH=.. prog`; `LESS=FRX
  less` is over-refused); a word naming git (`git`, `.../git`) is followed by
  a git option (`git -C <dir>`, `--git-dir=`, `-c`: that git could use a
  repository or configuration other than the judged ones); or a later word
  sets the environment (NAME=VALUE), holds
  `..` (`../x`, `-C ..`, `-C..`), holds a `/` or `~` without being exactly
  an absolute or `~/` path or a plain `--option=` followed by one (`-S/x`,
  `tools/x`, `~user/x`, and a sed script `s/a/b/`, over-refused), names such
  a path holding `:` `,` `=` `%` or `~` after its start, or holds a
  character outside [A-Za-z0-9_.,:@%+=-]. A later word that is such a path is
  resolved, and judged as a whole tree when it is a directory; a plain
  argument passes: its text names nothing outside git's working directory and
  PATH, which are judged where git runs a configured program (each --git-repo
  work tree and the candidate here and each Cargo git database, each verified
  above to be the directory git uses; a pinned checkout by
  require-private-tree and the gate's own check of git's view of it; this
  check's own `git var` and `git --exec-path` start no configured program and,
  in an --attest run, run in /, in no repository; since
  OD-XHOST-GATE-CWD-20261025 no git the run starts runs in the caller's
  working directory). After the `!` git strips, only blanks and newlines are
  skipped, as by /bin/sh: `!<U+00A0>/x` is the relative program
  `<U+00A0>/x` to the shell and refuses as one. An alias.* value without `!`
  is the argument list git runs itself after `git`, whose options can run a
  program (`fetch --upload-pack=/p`, `-c core.sshCommand=/p fetch`): its
  first word refuses when it is a git option (begins with `-`), and every
  word is read as a later word is. Every alias is judged, since a judged
  command can run git with one (`remote.origin.uploadpack = git x` runs
  alias x from the Clean work tree in the preflight's fetch; repair round 4).
  A path git reads from a key (core.hooksPath, core.attributesFile,
  core.excludesFile) or an origin is judged as git reads it, unstripped.
  git's exec path is judged as a tree.
  git runs here only after its binary and those files passed. A
  core.sharedRepository other than `umask` or false refuses: git would set
  the modes of what it writes there itself, past the run's umask 077 (LD-75);
* git's fetch transports, in every run (OD-XHOST-FETCH-TRANSPORT-20261016; a
  pinned checkout's `git fetch origin` or Cargo's git sources may use ssh
  whether or not an x86-64 executor is configured): ~/.ssh of both $HOME and
  the passwd home, and /etc/ssh, as trees; $SHELL (absolute, resolved as a
  tool; a relative value refuses, since ssh execv()s it with no PATH search)
  and /bin/sh (git's and ssh's shell); and the program each of
  GIT_SSH_COMMAND, GIT_SSH and GIT_PROXY_COMMAND in the environment and
  core.sshCommand and core.gitProxy in each repository's configuration names,
  every one that is set (not only the one git picks). A value that is empty,
  holds a character the shell gives a meaning beyond separating words, begins
  with an assignment (a shell command), or holds whitespace (a program git
  runs without a shell) refuses; otherwise its program, the first word, is
  judged as above. For GIT_SSH_COMMAND and core.sshCommand (shell commands)
  ANY later word then refuses (OD-XHOST-TRANSPORT-WORDS-20261024, superseding
  the later-word clause of OD-XHOST-FETCH-TRANSPORT-20261016): git runs them
  through the shell, so a later word can name or set a program or file git's
  child reads from its working directory, which no argument parser can judge;
  the remedy is to put options in ~/.ssh/config (judged). A protocol.allow or
  protocol.ext.allow other than `never`, and a GIT_ALLOW_PROTOCOL that lists
  ext, refuse: git's ext:: transport runs the command a remote URL names.

A missing path is accepted only when no other user can create it (the
directory it would be created in is judged without the sticky exemption).
The check judges the state when it runs; scripts/soundness_check.sh runs
the rest of an --attest run under umask 077, so what the run creates later
in a judged directory (which has no default ACL) is this user's alone.
A symlink's own mode bits and a socket's write bit are not judged (the
directory holding them decides who can replace them; writing a socket
connects to it). An entry that cannot be examined refuses.

NOT JUDGED: what a program loads from outside the trees named here (gcc's
cc1 and collect2 and the shared libraries below root-owned system
directories, a script's interpreter modules outside its import path, the
packages of a venv a leg activates itself), including the import path of
an interpreter a leg starts by another name than python3 (`python`,
`python3.12`: judged as PATH commands, not as interpreters) or that a
judged tool's own PATH change puts first for its children (a toolchain's
bin directory, judged as a tree); on macOS, which has no /proc/self/exe, a
compiled launcher that runs another binary under its own argv[0] (a `#!`
script doing so refuses); and what a judged program makes of a plain later
word of a git command key by its own rules (an option that makes it read a
file or use a directory of its own choosing, such as a login shell's `-l`
reading ~/.profile, or a credential helper's own configuration under $HOME:
the check reads the words' text, not each program's grammar), such as a
git a judged program starts by its own option in a directory outside every
judged work tree (`env -C /abs/dir git ...`: the directory is judged as a
tree, but the configuration of the repository git finds from there is not
held to the allowlist) or under another name, or in a bare repository
nested in a judged work tree that is no `.git` (`env -C <word>.git git
...`; neither git status nor Lake uses one); the keys of a repository
holding another directory with a .cargo Cargo reads
(soundness_attestation.py's Cargo configuration check runs `git ls-files`
there, with core.fsmonitor off on its command line, so that git runs no
configured program); a git another tool starts in a repository that is
none of the ones above (Lake's in a package outside a judged work tree,
for instance); what an ssh configuration names (ProxyCommand and the
other programs it runs, an Include outside ~/.ssh and /etc/ssh, and a
relative name in them, resolved in ssh's working directory: git's, or the
candidate checkout for soundness_remote.sh's own ssh in a full-scope run),
which is out of this check's scope by ruling, not a gap it claims to close:
ssh's configuration files are judged as files (~/.ssh and /etc/ssh as
trees, so no other user can write them), and the programs they name are
the user's own choice inside LD-73's host trust boundary, not "a program git
or a configured command runs" in the gate's claim
(OD-XHOST-GATE-CWD-20261025);
an absolute program a judged --git-repo's git starts from outside the judged
trees; the core.worktree of a local remote and of a submodule git directory
no populated path uses (git uses no work tree there during the run:
upload-pack needs none, and no git runs in an unpopulated submodule; a local
remote that is also a repository git uses a work tree of, a populated
submodule for instance, has its core.worktree judged as that one's);
a repository-local GIT_* variable a git newer than the supported versions
adds: soundness_attestation.py clears the fixed GIT_LOCAL_ENVIRONMENT (a
test checks it against the installed git), so outside an --attest run,
whose environment allowlist refuses every other GIT_* variable, such a
variable would reach that tool's git (a pre-push hook's check-record);
macOS extended ACLs (no API here; POSIX ACLs are judged on Linux); group
membership granted outside the group and account databases (PAM); a mode a
program the run starts sets explicitly past the umask (a build script's
chmod; git's core.sharedRepository is refused, above); an import hook (a
meta-path finder or path hook) that root-owned site code (a system .pth
line, a sitecustomize in the standard library) installs, and where it loads
from; the working directory of a python3 a leg starts with `-c` or `-` (the
leg's own: the candidate checkout, or a directory the test names or creates
under umask 077). The bash and python3 that started the run executed before
this check could judge them, with the caller's environment as bash read it
before its first line (BASH_ENV, SHELLOPTS, exported functions; the scrub
refuses each of those for the re-executed run): it judges those programs
then (the python3 PATH finds as a PATH entry, the pinned file it named as
--python3), so a refusal still stops the run; nothing else runs before it
(soundness_attestation.py's exec-scrubbed re-exec runs no program; finding
(7), R3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024), and the script the scrub
runs is the candidate's own (found without CDPATH, the same file bash runs,
and the candidate's scripts/soundness_check.sh read as a file;
OD-XHOST-GATE-CWD-20261025 repair rounds 2 and 3).

Prints a `host_boundary: judged <place>` line per judged place and a line per
accepted system-account file, then `host_boundary: PASS: ...` and exits 0;
or one `host_boundary: REFUSED <path> (<place>): <why>` line per refused
place (the first finding in a tree or PATH directory refuses it; at most
REFUSAL_LIMIT lines), then `host_boundary: FAIL: ...`, and exits 1. The FAIL
line counts the refusals of paths another user can write, with REMEDY, apart
from the refusals of any other kind (a git key off the allowlist, git's view
of a repository, a location that is not absolute, ...), whose REFUSED lines
give their own remedy: it never calls those a path another user can write.
"""

import argparse
import errno
import grp
import io
import os
import pwd
import re
import shutil
import stat
import struct
import subprocess
import sys

SYMLINK_HOP_LIMIT = 40
REFUSAL_LIMIT = 25
# NSS sources whose every member and account the grp/pwd enumeration lists.
ENUMERABLE_NSS_SOURCES = {"files", "compat", "systemd"}
NSSWITCH = "/etc/nsswitch.conf"
LOGIN_DEFS = "/etc/login.defs"
NOBODY_UID = 65534
GROUP_FILE = "/etc/group"
PASSWD_FILE = "/etc/passwd"
EXTRA_GROUP_VARIABLE = "SOUNDNESS_EXTRA_GROUP_FILE"
EXTRA_PASSWD_VARIABLE = "SOUNDNESS_EXTRA_PASSWD_FILE"
# The extended attributes that hold a POSIX access ACL and a directory's
# default ACL (Linux), their version and tags (linux/posix_acl_xattr.h,
# linux/posix_acl.h).
ACL_ACCESS_ATTRIBUTE = "system.posix_acl_access"
ACL_DEFAULT_ATTRIBUTE = "system.posix_acl_default"
ACL_EA_VERSION = 2
ACL_USER, ACL_GROUP_OBJ, ACL_GROUP, ACL_MASK, ACL_OTHER = 0x02, 0x04, 0x08, 0x10, 0x20
ACL_WRITE = 0x02
# The environment variables that make git read objects from another store
# than the repository's own objects/ and its alternates files.
GIT_OBJECT_STORE_VARIABLES = ("GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES")
# The environment's locations this check judges as trees or as roots of
# Cargo's configuration search. Cargo, rustup, elan, gate_env.sh and
# private_cache.py resolve a relative value against their working directory,
# which this check does not judge, so a value that is set and not absolute
# (an empty one included) refuses (LD-75 repair). HOME, XDG_CONFIG_HOME and
# TMPDIR are resolved below, which refuses a relative value too; a relative
# XDG_CACHE_HOME is ignored by the one cache-base rule.
LOCATION_VARIABLES = ("CARGO_HOME", "CARGO_TARGET_DIR", "RUSTUP_HOME", "ELAN_HOME", "SOUNDNESS_DEPS_DIR",
                      "ATPKG_BIN")
# The core.sharedRepository values under which git leaves the modes of what
# it creates to the umask (git_config_perm: `umask`, a false boolean, 0).
GIT_UMASK_SHARING = {"umask", "false", "no", "off", "0"}
# How many alternate object stores one git directory may chain through
# (git itself stops at a depth of 5).
ALTERNATES_LIMIT = 64
# The directory Cargo reads configuration from, in its working directory and
# in every ancestor of it.
CARGO_CONFIG_DIRECTORY = ".cargo"
NO_ACL_ERRNOS = {getattr(errno, name) for name in ("ENODATA", "ENOATTR", "ENOTSUP", "EOPNOTSUPP", "ENOSYS")
                 if hasattr(errno, name)}
# git configuration keys whose value runs a program (judge_git_command_value).
# git strips one leading `!` from an `alias.*` value and from a credential
# helper (`credential.helper`, `credential.<url>.helper`) and runs the rest
# as a shell command; it strips none from any other key. An `alias.*` value
# without the `!` is a list of git arguments.
GIT_COMMAND_KEY_SUFFIXES = (
    ".clean", ".smudge", ".process", ".textconv", ".command", ".driver", ".helper", ".program",
    ".uploadpack", ".receivepack", ".proxy", ".packobjectshook",
)
GIT_COMMAND_KEYS = {"core.fsmonitor", "core.pager", "core.editor", "core.askpass",
                    "sequence.editor", "gpg.program", "credential.helper",
                    # The `.command` suffix does not match these two; name them
                    # (OD-XHOST-TRANSPORT-WORDS-20261024). git runs
                    # core.alternateRefsCommand when a repository has alternates
                    # and gpg.ssh.defaultKeyCommand when commit.gpgSign is on
                    # (commit-tree, which the attestation runs).
                    "core.alternaterefscommand", "gpg.ssh.defaultkeycommand"}
# REPOSITORY-LOCAL CONFIGURATION (OD-XHOST-GIT-PROGRAM-KEYS-20261024). The set
# of configuration keys whose value names a program or a path git, a git helper
# (web--browse, difftool, mergetool, ...) or a git extension runs is open, so
# no list of such keys is complete. An --attest run's git processes therefore
# read no system or global configuration (GIT_CONFIG_NOSYSTEM=1 and
# GIT_CONFIG_GLOBAL naming the file this check writes, write_gate_git_config),
# and every key of the local, worktree and submodule configuration of a
# repository the run uses git in, and of every repository nested in its work
# tree (judge_repository_configuration), must be on this allowlist, or the run
# refuses by name. The allowlist holds data keys only, plus the few path keys
# judged elsewhere in this file (LOCAL_JUDGED_PATH_KEYS); it names no program.
LOCAL_CONFIG_SCOPES = frozenset({"local", "worktree"})
LOCAL_DATA_KEYS = frozenset({
    "core.repositoryformatversion", "core.filemode", "core.bare", "core.logallrefupdates", "core.ignorecase",
    "core.precomposeunicode", "core.symlinks", "core.autocrlf", "core.checkstat", "core.trustctime",
    "core.untrackedcache", "core.splitindex", "core.commitgraph", "core.multipackindex", "core.preloadindex",
    "core.protecthfs", "core.protectntfs", "core.quotepath", "core.abbrev", "core.compression",
    "core.loosecompression", "core.bigfilethreshold",
    "extensions.worktreeconfig", "extensions.objectformat", "extensions.refstorage", "extensions.noop",
    "user.name", "user.email", "user.useconfigonly", "author.name", "author.email", "committer.name",
    "committer.email",
    "init.defaultbranch", "remote.pushdefault", "fetch.prune", "fetch.prunetags", "gc.auto", "gc.autodetach",
    "maintenance.auto", "maintenance.strategy", "pull.rebase", "pull.ff", "push.default",
    "push.autosetupremote", "lfs.repositoryformatversion", "submodule.active", "submodule.recurse",
})
# submodule.recurse is a boolean selection, never a command. Every populated
# nested repository is still judged independently of this setting; in
# particular submodule.<name>.update remains a refused program-valued key.
# Three-level data keys, by section: the variable names allowed under any
# subsection (`remote.<name>.url`, `branch.<name>.merge`, ...). Not here, so
# refused: remote.<name>.uploadpack, .receivepack, .proxy and .vcs (each names
# a program), submodule.<name>.update (`!command`), and every other key.
LOCAL_DATA_SECTION_KEYS = {
    "remote": frozenset({"url", "pushurl", "fetch", "push", "tagopt", "prune", "prunetags", "mirror",
                         "skipdefaultupdate", "skipfetchall"}),
    "branch": frozenset({"remote", "merge", "rebase", "pushremote", "description", "vscode-merge-base"}),
    "submodule": frozenset({"url", "active", "branch"}),
}
# Two-level data keys allowed under any name of these sections.
LOCAL_DATA_SECTIONS = frozenset({"advice"})
# Path-valued keys allowed in a repository's configuration because judge_git
# judges each value (core.hooksPath as a tree, the two files resolved,
# core.sharedRepository's value, and core.worktree by judge_git_layout in
# every repository whose work tree git uses during the run: the candidate,
# each --git-repo, each Cargo git database and checkout, each nested
# repository, and a pinned checkout by soundness_check.sh. In a local remote
# and an unpopulated submodule git directory git uses no work tree during the
# run, so a core.worktree there is not judged; a local remote that is ALSO one
# of the repositories above, a populated submodule for instance, is judged as
# that too, its core.worktree included: REPOSITORY_JUDGEMENTS.)
LOCAL_JUDGED_PATH_KEYS = frozenset({"core.hookspath", "core.excludesfile", "core.attributesfile", "core.worktree",
                                    "core.sharedrepository"})
# The kinds of judgement made of a repository, each once per repository by
# directory identity (Boundary.judged, keyed on (identity, kind)). Which kinds
# a repository gets depends on how git can use it during the run, never on
# which path reached it first: a judgement of one kind never stands in for
# another (repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024; at 850f69fd0
# a local remote's configuration judgement, keyed on identity alone, made the
# nested judgement of the same repository, a populated submodule, return
# early, so git's view of its work tree was never asked and a core.worktree
# naming a 0777 directory passed).
REPOSITORY_JUDGEMENTS = {
    "configuration": "every scope of the configuration git reads there (judge_repository_configuration), with "
                     "its submodule git directories' configuration and its legacy remote files",
    "local configuration": "the same, the local and worktree scopes only (a full configuration judgement "
                           "includes it)",
    "nested walk": "every repository nested in its work tree, each given the nested judgement "
                   "(nested_repositories)",
    "nested repository": "as a repository nested in a judged work tree, which git status enters "
                         "(judge_nested_repository): its path, its tree, its git directories with their "
                         "alternates, git's view of its work tree (judge_git_layout), its local configuration and "
                         "its nested walk",
    "local remote": "as a local repository a remote location names, where git runs upload-pack "
                    "(judge_local_remote): its tree, its git directories with their alternates, its local "
                    "configuration and its nested walk (upload-pack uses no work tree)",
}
# Keys whose value is a remote's location: a local path or file:// URL names
# a repository git's upload-pack runs in, which judge_local_remote judges as a
# repository (tree, git directories and configuration).
REMOTE_URL_NAMES = {"remote": ("url", "pushurl"), "submodule": ("url",)}
# What the gate's own git configuration file carries over from the user's
# system and global configuration (write_gate_git_config): the credential
# helpers git needs for the https origins the preflight fetches (this host's
# Clean, AY and aterm origins are private GitHub repositories), each judged as
# a command; the commit identity the attestation's `git commit-tree` needs;
# and core.excludesFile (a judged file), so a checkout's status means what it
# meant before. Nothing else: no alias, pager, editor, filter, diff, merge or
# browser setting, no url.*.insteadOf, http.* or include.
CARRIED_KEYS = frozenset({"user.name", "user.email", "author.name", "author.email", "committer.name",
                          "committer.email", "core.excludesfile"})
CARRIED_CREDENTIAL_NAMES = frozenset({"helper", "username", "usehttppath"})
# Settings the gate's file sets itself: a fetch never recurses into a
# submodule (no submodule fetch is needed, and none runs).
GATE_GIT_SETTINGS = (("fetch", None, "recurseSubmodules", "false"),)
GATE_GIT_CONFIG_LINE = "host_boundary: gate git configuration "
# The system file Cargo's built-in libgit2 reads (its sysconfdir on Linux and
# macOS), whatever GIT_CONFIG_SYSTEM or GIT_CONFIG_NOSYSTEM say (judge_git).
LIBGIT2_SYSTEM_CONFIG = "/etc/gitconfig"
LOCAL_KEY_REMEDY = ("remedy: remove it from that repository's configuration (`git -C <repo> config --unset-all "
                    "<key>`); an --attest run's git reads no configuration key this check has not judged "
                    "(OD-XHOST-GIT-PROGRAM-KEYS-20261024)")
# The programs a fetch's transport runs that the environment or git's
# configuration name (git's connect.c): GIT_SSH_COMMAND and core.sshCommand
# hold a command git runs through the shell; GIT_SSH, GIT_PROXY_COMMAND and
# core.gitProxy (before its ` for <domain>`) name one program. git picks one
# of them; every one that is set is judged, in every run
# (OD-XHOST-FETCH-TRANSPORT-20261016). The flag says whether the value is a
# shell command.
TRANSPORT_VARIABLES = (("GIT_SSH_COMMAND", True), ("GIT_SSH", False), ("GIT_PROXY_COMMAND", False))
TRANSPORT_KEYS = {"core.sshcommand": True, "core.gitproxy": False}
# The configuration keys that can let git's ext:: transport run the command a
# remote URL names; only `never` passes.
EXT_PROTOCOL_KEYS = ("protocol.allow", "protocol.ext.allow")
# Characters the shell gives a meaning beyond separating words (quoting,
# expansion, globbing, redirection, a further command, a comment): a
# transport program's value holding one is refused, never parsed.
SHELL_SYNTAX = frozenset("|&;<>()$`\\\"'*?[]{}#\n\r")
# What the shell splits a command's words on (its default IFS). Python's
# str.split() also splits on other whitespace (U+00A0, ...), which the shell
# keeps inside a word: `ssh<U+00A0>tools/x` is one relative path to it.
SHELL_WORD_SEPARATORS = re.compile("[ \t\n]+")
# A later word that sets the environment (`NAME=VALUE`, NAME a shell
# identifier): it can change which program or file a shell command resolves
# (a PATH it sets, for instance), so it is refused in a git command key, and
# any later word at all is refused in a transport shell command
# (OD-XHOST-TRANSPORT-WORDS-20261024).
ENVIRONMENT_ASSIGNMENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*=")
# A later word of a git command key (and every word of an `alias.*` value
# without `!`) that holds no `/` and no `~` passes as a PLAIN ARGUMENT only
# when it is made of these characters (and holds no `..`): letters, digits
# and `_ . , : @ % + = -` (`%` for git's own placeholders such as a filter's
# `%f`). Its text then names no directory outside git's working directory
# and PATH. Anything else refuses (OD-XHOST-TRANSPORT-WORDS-20261024, repair
# round 2).
PLAIN_COMMAND_WORD = re.compile(r"[A-Za-z0-9_.,:@%+=-]+")
# The words a shell reads as reserved where a command begins (POSIX
# XCU 2.4, and bash's and ksh's `[[`, `]]`, `function`, `select`, `coproc`
# and `time`). A shell command whose first word is one of them, or begins
# with `!` (a second `!` after the one git strips: `!! /x` is `! /x` to the
# shell, which runs /x), is not a program this check can judge by name, so it
# refuses by name (repair round 4 of OD-XHOST-TRANSPORT-WORDS-20261024).
SHELL_RESERVED_WORDS = frozenset(("!", "{", "}", "if", "then", "else", "elif", "fi", "case", "esac", "for",
                                  "while", "until", "do", "done", "in", "time", "[[", "]]", "function", "select",
                                  "coproc"))
# The text of an absolute or `~/` path a later word names (after its leading
# `/` or `~/`): only these characters, so a program cannot split it into a
# path list (`:` `,` `=`) and neither git nor the shell substitutes inside it
# (`%` `~`). Anything else refuses.
PLAIN_PATH_TEXT = re.compile(r"[A-Za-z0-9_.@+/-]*")
# A canonical path at or below one of these names the RESOLVING process's own
# view of the filesystem, not the view of the program that would later use the
# path: on Linux /proc is procfs (/proc/self, /proc/thread-self, /proc/<pid>)
# and /dev/fd is a symlink to /proc/self/fd; on macOS /dev/fd is an fdescfs
# mount whose `..` escapes. A path git's child runs in its own working
# directory would see a different /proc/self and a different /dev/fd, so such a
# path is judged in the wrong place and is refused outright (finding (1) of the
# X-HOST-P13 round-5 verifier; OD-XHOST-TRANSPORT-WORDS-20261024). /dev/null and
# /dev/shm are not below either and keep passing.
RESTRICTED_SELF_VIEW_PREFIXES = ("/proc", "/dev/fd")
TRANSPORT_REMEDY = ("remedy: name the program alone (an absolute path, or a bare name found on PATH) and put every "
                    "option, identity file and ProxyCommand in ~/.ssh/config, which this check judges "
                    "(OD-XHOST-TRANSPORT-WORDS-20261024)")
GIT_COMMAND_REMEDY = ("remedy: name the program by an absolute path or a bare PATH name, with no shell "
                      "metacharacter, no environment assignment and no `..`, give every path argument as a separate "
                      "absolute or ~/ path word (or `--option=/path`), and put anything else, such as a sed script, "
                      "in a file named that way or in a wrapper script named by an absolute path "
                      "(OD-XHOST-TRANSPORT-WORDS-20261024)")
REMEDY = ("remedy: make it writable by you alone (`chmod go-w <path>`; `setfacl -b <path>` for an ACL; "
          "reinstall it as your own if another user may already have changed it), make its group one with "
          "no other member, or take it out of what the run executes or reads (PATH, the environment, the git "
          "configuration); an --attest run executes nothing else until then (LD-73)")


class Accounts:
    """Who besides this user is in a group, from the group and account
    databases this module's docstring names. The extra files only ADD: their
    entries add members, accounts and uid mappings, but a gid is known only
    from the host's group databases and a name has an account only in the
    host's account databases (ruling LD-75), so neither file can turn a group
    with no entry or a member with no account into a private group."""

    def __init__(self, euid, extra_group=None, extra_passwd=None):
        self.euid = euid
        self.members = {}         # gid -> set of member names
        self.known_gids = set()   # gids a HOST group entry names
        self.uids = {}            # account name -> set of uids (host and extra entries)
        self.host_accounts = set()  # account names a HOST account entry names
        self.primary = {}         # gid -> set of (name, uid) whose primary group it is
        self.unenumerable = []    # why some members may be invisible here
        self.sources = []
        self._read_group_file(GROUP_FILE, host=True)
        if extra_group:
            self._read_group_file(extra_group, host=False)
        self._read_passwd_file(PASSWD_FILE, host=True)
        if extra_passwd:
            self._read_passwd_file(extra_passwd, host=False)
        try:
            for entry in grp.getgrall():
                self._add_group(entry.gr_name, entry.gr_gid, entry.gr_mem, host=True)
        except OSError:
            pass
        try:
            for entry in pwd.getpwall():
                self._add_account(entry.pw_name, entry.pw_uid, entry.pw_gid, host=True)
        except OSError:
            pass
        self._read_nsswitch()
        self._others = {}

    def _add_group(self, name, gid, members, host):
        if host:
            self.known_gids.add(gid)
        self.members.setdefault(gid, set()).update(member for member in members if member)

    def _add_account(self, name, uid, gid, host):
        if host:
            self.host_accounts.add(name)
        self.uids.setdefault(name, set()).add(uid)
        self.primary.setdefault(gid, set()).add((name, uid))

    def _lines(self, path):
        try:
            with open(path, "rb") as handle:
                data = handle.read()
        except FileNotFoundError:
            return []
        self.sources.append(path)
        return data.decode("utf-8", "replace").splitlines()

    def _read_group_file(self, path, host):
        for line in self._lines(path):
            if line[:1] in ("+", "-"):
                self.unenumerable.append("{} has a compat `{}` line".format(path, line[:1]))
                continue
            fields = line.split(":")
            if len(fields) < 4 or not fields[2].strip().isdigit():
                continue
            self._add_group(fields[0], int(fields[2]), fields[3].strip().split(","), host)

    def _read_passwd_file(self, path, host):
        for line in self._lines(path):
            if line[:1] in ("+", "-"):
                self.unenumerable.append("{} has a compat `{}` line".format(path, line[:1]))
                continue
            fields = line.split(":")
            if len(fields) < 4 or not fields[2].strip().isdigit() or not fields[3].strip().isdigit():
                continue
            self._add_account(fields[0], int(fields[2]), int(fields[3]), host)

    def _read_nsswitch(self):
        if not sys.platform.startswith("linux"):
            return
        for line in self._lines(NSSWITCH):
            database, _, sources = line.split("#", 1)[0].partition(":")
            if database.strip() not in ("passwd", "group"):
                continue
            for source in sources.split():
                if source.startswith("[") or source.endswith("]"):
                    continue
                if source not in ENUMERABLE_NSS_SOURCES:
                    self.unenumerable.append("{} names the {} source `{}`".format(NSSWITCH, database.strip(), source))

    def _uids_of(self, name):
        uids = set(self.uids.get(name, ()))
        try:
            uids.add(pwd.getpwnam(name).pw_uid)
        except KeyError:
            pass
        return uids

    def _has_host_account(self, name):
        if name in self.host_accounts:
            return True
        try:
            pwd.getpwnam(name)
            return True
        except KeyError:
            return False

    def others(self, gid):
        """The members of group `gid` other than this user and root (by
        name, with why), or a reason the members cannot be known; empty when
        this user is its only member."""
        if gid in self._others:
            return self._others[gid]
        others = []
        members = set(self.members.get(gid, ()))
        known = gid in self.known_gids
        try:
            entry = grp.getgrgid(gid)
            known = True
            members.update(member for member in entry.gr_mem if member)
        except KeyError:
            pass
        if not known:
            others.append("no group entry names gid {}, so its members are unknown".format(gid))
        for name in sorted(members):
            # Every uid any database maps the name to; a name the host's
            # account databases do not know stays another member even when
            # an extra file maps it to this user.
            if self._uids_of(name) - {self.euid, 0}:
                others.append("member {}".format(name))
            elif not self._has_host_account(name):
                others.append("member {} has no account".format(name))
        for name, uid in sorted(self.primary.get(gid, ())):
            if uid not in (self.euid, 0):
                others.append("{} (uid {}) has it as primary group".format(name, uid))
        if self.unenumerable:
            others.append("its members cannot all be listed: " + "; ".join(sorted(set(self.unenumerable))))
        self._others[gid] = others
        return others

    def group_label(self, gid):
        try:
            return "group {} (gid {})".format(grp.getgrgid(gid).gr_name, gid)
        except KeyError:
            return "gid {}".format(gid)


def _mode(metadata):
    return stat.S_IMODE(metadata.st_mode)


def _restricted_self_view(path):
    """The `/proc` or `/dev/fd` prefix `path` (a canonical path) is at or
    below, or None. Such a path names the checking process's own filesystem
    view, not the view of the program that would use it (finding (1))."""
    for prefix in RESTRICTED_SELF_VIEW_PREFIXES:
        if path == prefix or path.startswith(prefix + os.sep):
            return prefix
    return None


def _self_view_on_the_way(path):
    """The /proc or /dev/fd prefix the absolute `path` reaches at any canonical
    position while it is followed as the kernel follows it (every symlink's
    literal target, `..` against the canonical position), or None. It judges
    nothing: Boundary.resolve does that, with the same test at every hop.
    A missing component ends the walk (nothing below it is reached)."""
    current = os.sep
    pending = [part for part in path.split(os.sep) if part]
    hops = 0
    while pending:
        name = pending.pop(0)
        if name == os.curdir:
            continue
        if name == os.pardir:
            current = os.path.dirname(current)
            continue
        entry = os.path.join(current, name)
        restricted = _restricted_self_view(entry)
        if restricted:
            return restricted
        try:
            metadata = os.lstat(entry)
        except OSError:
            return None
        if stat.S_ISLNK(metadata.st_mode):
            hops += 1
            if hops > SYMLINK_HOP_LIMIT:
                return None
            target = os.readlink(entry)
            if os.path.isabs(target):
                current = os.sep
            pending = [part for part in target.split(os.sep) if part] + pending
            continue
        current = entry
    return None


# -- POSIX ACLs (Linux) ------------------------------------------------
# One reader and one reading of an ACL, shared with scripts/private_cache.py's
# tree rule (`require_private_tree`), which passes an `accounts` under which
# every group counts as having another member (its strict rule). `accounts`
# is anything with `others(gid)` (why the group has a member other than this
# user, empty when it has none) and `group_label(gid)`.
def read_acl(path, attribute, what):
    """The entries (tag, perm, id) of the POSIX ACL `attribute` of `path`
    and None; (None, None) when it has none, or the platform has no
    extended-attribute call (macOS); or (None, [why it cannot be read])
    (`what` names the ACL in that reason)."""
    getxattr = getattr(os, "getxattr", None)
    if getxattr is None:
        return None, None
    try:
        data = getxattr(path, attribute, follow_symlinks=False)
    except OSError as error:
        if error.errno in NO_ACL_ERRNOS:
            return None, None
        return None, ["its {} cannot be read ({})".format(what, error.strerror or error)]
    if len(data) < 4 or (len(data) - 4) % 8 or struct.unpack_from("<I", data)[0] != ACL_EA_VERSION:
        return None, ["its {} has an unknown format".format(what)]
    return [struct.unpack_from("<HHI", data, offset) for offset in range(4, len(data), 8)], None


def default_acl_writers(path, metadata, euid, accounts):
    """Who besides `euid` the POSIX default ACL of the directory `path`
    (whose lstat is `metadata`) lets write an entry created in it: a new
    entry's access ACL is that default ACL (its group class still under the
    default mask), whatever the umask. None when it has no default ACL."""
    entries, unreadable = read_acl(path, ACL_DEFAULT_ATTRIBUTE, "default ACL")
    if unreadable:
        return unreadable
    if entries is None:
        return None
    mask = next((perm for tag, perm, _ in entries if tag == ACL_MASK), None)
    masked = mask is not None and not mask & ACL_WRITE
    writers = []
    for tag, perm, ident in entries:
        if not perm & ACL_WRITE:
            continue
        if tag == ACL_OTHER:
            writers.append("its default ACL lets every user write what is created in it")
        elif masked:
            continue
        elif tag == ACL_USER and ident not in (euid, 0):
            writers.append("its default ACL lets uid {} write what is created in it".format(ident))
        elif tag in (ACL_GROUP_OBJ, ACL_GROUP):
            # A new entry's owning group is the directory's (set-group-ID)
            # or the creator's: both are judged.
            gids = {metadata.st_gid, os.getegid()} if tag == ACL_GROUP_OBJ else {ident}
            for gid in sorted(gids):
                others = accounts.others(gid)
                if others:
                    writers.append("its default ACL lets {} write what is created in it, and {}".format(
                        accounts.group_label(gid), "; ".join(others)))
    return writers


def access_acl_writers(path, metadata, euid, accounts):
    """Who besides the owner (and `euid`) a POSIX access ACL lets write
    `path` (whose lstat is `metadata`), or None when it has no ACL (then the
    group bits are the group's)."""
    entries, unreadable = read_acl(path, ACL_ACCESS_ATTRIBUTE, "ACL")
    if unreadable:
        return unreadable
    if entries is None:
        return None
    mask = next((perm for tag, perm, _ in entries if tag == ACL_MASK), None)
    writers = []
    for tag, perm, ident in entries:
        if not perm & ACL_WRITE or (mask is not None and not mask & ACL_WRITE):
            continue
        if tag == ACL_USER and ident not in (euid, 0):
            writers.append("its ACL lets uid {} write it".format(ident))
        elif tag in (ACL_GROUP_OBJ, ACL_GROUP):
            gid = metadata.st_gid if tag == ACL_GROUP_OBJ else ident
            others = accounts.others(gid)
            if others:
                writers.append("its ACL lets {} write it, and {}".format(accounts.group_label(gid), "; ".join(others)))
    return writers


def login_uid_min():
    """The first uid of a login account: UID_MIN in /etc/login.defs (Linux),
    else 500 on macOS and 1000 elsewhere. Accounts below it are the system's."""
    if sys.platform == "darwin":
        return 500
    try:
        with open(LOGIN_DEFS, "r", encoding="utf-8", errors="replace") as handle:
            for line in handle:
                fields = line.split()
                if len(fields) >= 2 and fields[0] == "UID_MIN" and fields[1].isdigit():
                    return int(fields[1])
    except OSError:
        pass
    return 1000


class Boundary:
    """Judges paths against ANOTHER USER CAN WRITE, collecting refusals."""

    def __init__(self, accounts, euid=None):
        self.accounts = accounts
        self.euid = os.geteuid() if euid is None else euid
        self.refusals = []
        # How many of them refuse a path another user can write (the rest
        # refuse a setting, location, repository or key for another reason).
        self.writable_refusals = 0
        self.entries = 0
        self.trees = []
        self.places = []
        self._lookup_cache = {}
        self._path_dirs = set()
        self._refused = set()
        self.system_owned = set()
        self.uid_min = login_uid_min()
        # The system and global (raw key, raw value) pairs the gate's git
        # configuration carries (judge_git).
        self.carried = None
        # Every directory a judge_tree walk listed that holds an entry named
        # `.git` (canonical paths): a repository nested in the work tree of one
        # the run uses git in is found here (repair round 2 of
        # OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        self.git_holders = set()
        # The judgements made of each repository, keyed on (directory
        # identity, kind of judgement): REPOSITORY_JUDGEMENTS. Each kind is
        # made once per repository, whichever path reached it first, and a
        # judgement of one kind never stands in for another: a repository a
        # local remote names (its configuration judged, no work tree used) that
        # is also nested in a judged work tree (git status enters it) still gets
        # the nested judgement, git's view of its work tree included (repair
        # round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        self.judged = set()

    # -- verdicts ------------------------------------------------------
    def first_judgement(self, repo, kind):
        """True, recording it, when the repository at `repo` (by directory
        identity) has not yet been given the judgement `kind`
        (REPOSITORY_JUDGEMENTS); False when it has."""
        if self.has_judgement(repo, kind):
            return False
        self.judged.add((_directory_identity(repo), kind))
        return True

    def has_judgement(self, repo, kind):
        """Whether the repository at `repo` (by directory identity) has been
        given the judgement `kind` (REPOSITORY_JUDGEMENTS)."""
        if kind not in REPOSITORY_JUDGEMENTS:
            raise ValueError("unknown repository judgement {!r}".format(kind))
        return (_directory_identity(repo), kind) in self.judged

    def refuse(self, path, place, why, writable=False):
        """Record one refusal; `writable` when the reason is that another user
        can write `path` (problem), which REMEDY answers (the FAIL line names
        it only for those)."""
        if path in self._refused:
            return
        self._refused.add(path)
        if len(self.refusals) < REFUSAL_LIMIT:
            self.refusals.append("{} ({}): {}".format(path, place, why))
            self.writable_refusals += writable
        else:
            raise _TooMany()

    def _default_acl_writers(self, path, metadata):
        return default_acl_writers(path, metadata, self.euid, self.accounts)

    def _acl_writers(self, path, metadata):
        return access_acl_writers(path, metadata, self.euid, self.accounts)

    def _system_owned_in_root_directory(self, path, uid):
        """Whether `path`, owned by `uid`, is a system package's file: `uid`
        is a system account (below UID_MIN) and the directory holding `path`
        is root's. Only that account and root can then change it, and no
        login user (/usr/sbin/lldpcli is setuid _lldpd on Ubuntu)."""
        if uid >= self.uid_min or uid == NOBODY_UID:
            return False
        parent = os.path.dirname(path.rstrip(os.sep)) or os.sep
        try:
            if os.lstat(parent).st_uid != 0:
                return False
        except OSError:
            return False
        self.system_owned.add("{} (uid {})".format(path, uid))
        return True

    def problem(self, path, metadata, sticky_entry=None, default_acl=True):
        """Why another user can write `path` (whose lstat is `metadata`), or
        None. `sticky_entry` is the lstat of the entry looked up in a
        directory `path` (a sticky directory then protects it). Without
        `default_acl`, a directory's default ACL is left to the caller."""
        if metadata.st_uid not in (self.euid, 0) and not self._system_owned_in_root_directory(
                path, metadata.st_uid):
            try:
                owner = pwd.getpwuid(metadata.st_uid).pw_name
            except KeyError:
                owner = "no account"
            return "owned by uid {} ({}), another user, who can change it".format(metadata.st_uid, owner)
        if default_acl and stat.S_ISDIR(metadata.st_mode):
            # Whatever its own mode: a default ACL decides who can write what
            # is created in the directory later, and overrides the umask.
            defaults = self._default_acl_writers(path, metadata)
            if defaults:
                return "; ".join(defaults)
        # A symlink's own mode means nothing (its parent decides who can
        # replace it), and a socket's write bit grants connecting, not
        # changing a file.
        if stat.S_ISLNK(metadata.st_mode) or stat.S_ISSOCK(metadata.st_mode) or not metadata.st_mode & 0o022:
            return None
        if (sticky_entry is not None and stat.S_ISDIR(metadata.st_mode) and metadata.st_mode & stat.S_ISVTX
                and sticky_entry.st_uid in (self.euid, 0)):
            return None
        if path == os.devnull and stat.S_ISCHR(metadata.st_mode):
            return None
        if metadata.st_mode & 0o002:
            return "writable by every user (mode {:04o})".format(_mode(metadata))
        writers = self._acl_writers(path, metadata)
        if writers is None:
            others = self.accounts.others(metadata.st_gid)
            if not others:
                return None
            return "group-writable (mode {:04o}) by {}, which has another member: {}".format(
                _mode(metadata), self.accounts.group_label(metadata.st_gid), "; ".join(others))
        if writers:
            return "writable through its ACL (mode {:04o}): {}".format(_mode(metadata), "; ".join(writers))
        return None

    def judge(self, path, metadata, place):
        self.entries += 1
        why = self.problem(path, metadata)
        if why:
            self.refuse(path, place, why, writable=True)

    def _judge_lookup(self, directory, entry_metadata, place):
        """The directory `directory` (canonical) is looked up in for one
        entry (its lstat, or None when missing): nobody else may replace,
        rename or create that entry."""
        cached = self._lookup_cache.get(directory)
        if cached is None:
            metadata = os.lstat(directory)
            cached = (metadata, self.problem(directory, metadata))
            self._lookup_cache[directory] = cached
            self.entries += 1
        metadata, why = cached
        if why and entry_metadata is not None:
            why = self.problem(directory, metadata, sticky_entry=entry_metadata)
        if why:
            self.refuse(directory, place, why + (" (a name looked up in it)" if entry_metadata is not None
                                                  else " (a missing name could be created in it)"),
                        writable=True)

    # -- resolution ----------------------------------------------------
    def resolve(self, path, place, scratch=False):
        """Follow the absolute `path` as the kernel resolves it, judging the
        directory of every lookup and, at the end, the entry itself (a
        directory as one whose entries are used; with `scratch`, as one the
        legs only create their own entries in, which the sticky bit
        protects). Returns the canonical path, or None when it does not exist
        (after judging that no other user can create it)."""
        if not os.path.isabs(path):
            self.refuse(path, place, "is not an absolute path, so it depends on the working directory")
            return None
        current = os.sep
        pending = [part for part in path.split(os.sep) if part]
        hops = 0
        while pending:
            name = pending.pop(0)
            if name == os.curdir:
                continue
            if name == os.pardir:
                current = os.path.dirname(current)
                continue
            entry = os.path.join(current, name)
            # `current` carries no symlink and no `.`/`..`, so `entry` is a
            # canonical position: refuse it before lstat or following it when
            # it enters /proc or /dev/fd (finding (1)).
            restricted = _restricted_self_view(entry)
            if restricted:
                self.refuse(entry, place, "resolves into {}, which names the checking process's own view of the "
                            "filesystem (its /proc/self, /proc/thread-self or /dev/fd), not the view the program "
                            "that would use this path has from its own working directory, so what this check judges "
                            "is not what that program would reach; remedy: name the target by a real path outside "
                            "/proc and /dev/fd (OD-XHOST-TRANSPORT-WORDS-20261024)".format(restricted))
                return None
            try:
                metadata = os.lstat(entry)
            except OSError as error:
                if error.errno not in (errno.ENOENT, errno.ENOTDIR):
                    self.refuse(entry, place, "cannot be examined ({})".format(error.strerror or error))
                    return None
                self._judge_lookup(current, None, place)
                return None
            self._judge_lookup(current, metadata, place)
            if stat.S_ISLNK(metadata.st_mode):
                hops += 1
                if hops > SYMLINK_HOP_LIMIT:
                    self.refuse(path, place, "resolves through more than {} symlinks".format(SYMLINK_HOP_LIMIT))
                    return None
                target = os.readlink(entry)
                if os.path.isabs(target):
                    current = os.sep
                pending = [part for part in target.split(os.sep) if part] + pending
                continue
            if pending and not stat.S_ISDIR(metadata.st_mode):
                # The kernel refuses a name below a file: nothing is reached.
                self.judge(entry, metadata, place)
                return None
            current = entry
        metadata = os.lstat(current)
        if scratch:
            self.entries += 1
            mine = os.stat_result((stat.S_IFDIR, 0, 0, 0, self.euid, 0, 0, 0, 0, 0))
            why = self.problem(current, metadata, sticky_entry=mine)
            if why:
                self.refuse(current, place, why, writable=True)
        else:
            self.judge(current, metadata, place)
        return current

    def judge_scratch_directory(self, path, place):
        """`path` is a directory the legs create their own entries in (a
        temporary directory): its resolution is judged as everywhere, and
        the directory itself may be writable by others only with the sticky
        bit, which keeps what this user creates there this user's."""
        self.resolve(path, place, scratch=True)

    def _covered(self, path):
        return any(path == root or path.startswith(root.rstrip(os.sep) + os.sep) for root in self.trees)

    def judge_tree(self, path, place):
        """`path` and every entry below it; a symlink's target is resolved
        hop by hop and, when it is a directory outside every judged tree,
        judged as a tree of its own."""
        before = len(self.refusals)
        root = self.resolve(path, place)
        pending_roots = [root] if root is not None and os.path.isdir(root) else []
        while pending_roots:
            root = pending_roots.pop()
            if self._covered(root):
                continue
            self.trees.append(root)
            stack = [root]
            while stack:
                if len(self.refusals) > before:
                    # One finding per tree is enough to refuse it; the
                    # report goes on to the other places.
                    return
                directory = stack.pop()
                try:
                    names = os.listdir(directory)
                except (FileNotFoundError, NotADirectoryError):
                    continue  # removed meanwhile (a concurrent build's target/)
                except OSError as error:
                    self.refuse(directory, place, "cannot be listed ({})".format(error.strerror or error))
                    continue
                if ".git" in names:
                    # A repository's top (or a nested repository's): recorded
                    # for nested_repositories.
                    self.git_holders.add(directory)
                for name in names:
                    entry = os.path.join(directory, name)
                    # The tree's root and every directory below it are
                    # canonical, so a tree that holds /proc or /dev/fd (one
                    # rooted at / or /dev) reaches the checker's own view
                    # there: refuse, as resolve does (finding (1)).
                    restricted = _restricted_self_view(entry)
                    if restricted:
                        self.refuse(entry, place, "is {}, which names the checking process's own view of the "
                                    "filesystem, so this tree cannot be judged as another process would see it "
                                    "(OD-XHOST-TRANSPORT-WORDS-20261024)".format(restricted))
                        return
                    try:
                        metadata = os.lstat(entry)
                    except FileNotFoundError:
                        continue
                    if stat.S_ISLNK(metadata.st_mode):
                        self.entries += 1
                        target = self.resolve(entry, place)
                        if target is not None and os.path.isdir(target) and not self._covered(target):
                            pending_roots.append(target)
                        continue
                    self.judge(entry, metadata, place)
                    if stat.S_ISDIR(metadata.st_mode):
                        stack.append(entry)

    def judge_search_path(self, value):
        """Every PATH directory and every command in it."""
        for entry in value.split(os.pathsep):
            place = "PATH entry {!r}".format(entry)
            if not entry or not os.path.isabs(entry):
                self.refuse(entry or "(empty)", place, "a relative PATH entry is looked up from the working "
                            "directory, which another user's files may be in")
                continue
            before = len(self.refusals)
            directory = self.resolve(entry, place)
            if directory is None or not os.path.isdir(directory) or directory in self._path_dirs \
                    or len(self.refusals) > before:
                continue
            self._path_dirs.add(directory)
            self.places.append("PATH {}".format(directory))
            try:
                names = sorted(os.listdir(directory))
            except OSError as error:
                self.refuse(directory, place, "cannot be listed ({})".format(error.strerror or error))
                continue
            for name in names:
                command = os.path.join(directory, name)
                try:
                    metadata = os.lstat(command)
                except FileNotFoundError:
                    continue
                if stat.S_ISLNK(metadata.st_mode):
                    self.entries += 1
                    self.resolve(command, place)
                else:
                    self.judge(command, metadata, place)

    def judge_cargo_ancestry(self, path, place):
        """Cargo merges `.cargo/config.toml` (and `.cargo/config`) from its
        working directory and from every ancestor of it, read at each run:
        no canonical ancestor of `path` (`path` included) up to / may be a
        directory another user can create an entry in, sticky or not (they
        could create its `.cargo` after this check; ruling LD-75), unless it
        is sticky and already holds a `.cargo` directory of this user's (or
        root's), which is then judged as a tree. A component of `path` that
        does not exist yet is skipped (the rule judges whatever exists above
        it). A `path` that is not absolute refuses: where Cargo would search
        depends on the working directory (LD-75 repair). A directory whose
        default ACL lets another user write what is created in it refuses
        too, with that reason (the run may create entries there), whether or
        not it holds a `.cargo`."""
        if not path or not os.path.isabs(path):
            self.refuse(path or "(empty)", place, "is not an absolute path, so Cargo's configuration search above "
                        "it depends on the working directory (LD-75)")
            return
        # A path whose resolution enters /proc or /dev/fd refuses (finding (1);
        # OD-XHOST-TRANSPORT-WORDS-20261024). It is followed hop by hop first,
        # as the kernel follows it (a /proc component, or a symlink into
        # /proc/self/cwd, which os.path.realpath would follow into the
        # CHECKER's own cwd), so realpath never runs on such a path (realpath
        # of /proc/1/cwd raises PermissionError; repair round 3). That walk
        # stops at a missing component, where realpath goes on lexically
        # (`<missing>/../proc/self/cwd` is the checker's cwd to realpath, and
        # a `mkdir -p` of it creates <missing> and then lands in /proc), so
        # the lexical normal form and the realpath are tested too, as
        # f7919800a tested them (repair round 4 restores that test, which
        # a6cbba41b had dropped), and a realpath that fails refuses.
        restricted = _self_view_on_the_way(path) or _restricted_self_view(os.path.normpath(path))
        if restricted:
            self.refuse(path, place, "resolves into {}, the checking process's own filesystem view, not the view "
                        "Cargo would have from its working directory (OD-XHOST-TRANSPORT-WORDS-20261024)".format(
                            restricted))
            return
        try:
            directory = os.path.realpath(path)
        except OSError as error:
            self.refuse(path, place, "cannot be examined ({})".format(error.strerror or error))
            return
        restricted = _restricted_self_view(directory)
        if restricted:
            self.refuse(path, place, "resolves into {} (its canonical path is {}), the checking process's own "
                        "filesystem view, not the view Cargo would have from its working directory "
                        "(OD-XHOST-TRANSPORT-WORDS-20261024)".format(restricted, directory))
            return
        while True:
            try:
                metadata = os.lstat(directory)
            except OSError as error:
                if error.errno not in (errno.ENOENT, errno.ENOTDIR):
                    self.refuse(directory, place, "cannot be examined ({})".format(error.strerror or error))
                    return
                metadata = None
            if metadata is not None and stat.S_ISDIR(metadata.st_mode):
                self.entries += 1
                self._judge_cargo_directory(directory, metadata, place)
            parent = os.path.dirname(directory)
            if parent == directory:
                return
            directory = parent

    def _judge_cargo_directory(self, directory, metadata, place):
        """`directory` is an ancestor Cargo reads a `.cargo` from: refused
        when another user can create entries in it (and so its `.cargo`),
        unless it is sticky and holds this user's or root's `.cargo`, which
        is then judged as a tree; and refused when its default ACL lets
        another user write what is created in it (reported as that, not as a
        `.cargo` another user can create)."""
        reasons = []
        why = self.problem(directory, metadata, default_acl=False)
        if why:
            dot_cargo = os.path.join(directory, CARGO_CONFIG_DIRECTORY)
            try:
                held = os.lstat(dot_cargo)
            except FileNotFoundError:
                held = None
            if (held is not None and metadata.st_mode & stat.S_ISVTX and stat.S_ISDIR(held.st_mode)
                    and held.st_uid in (self.euid, 0)):
                self.judge_tree(dot_cargo, place + ": the .cargo Cargo reads in " + directory)
            else:
                reasons.append("{}, so another user can create {} there, whose configuration Cargo reads in every "
                               "directory below it".format(why, dot_cargo))
        opened = self._default_acl_writers(directory, metadata)
        if opened:
            reasons.append("{}, so an entry created in it is open to another user whatever the umask".format(
                "; ".join(opened)))
        if reasons:
            self.refuse(directory, place, "; and ".join(reasons) + " (LD-75)", writable=True)


class _TooMany(Exception):
    pass


def git_directories(repo):
    """The git directory and common directory of the repository at `repo`,
    read from its `.git` (a directory, or a `gitdir:` file and the
    `commondir` file it leads to) without running git; a bare repository is
    its own git directory. Empty when `repo` holds no repository."""
    dot_git = os.path.join(repo, ".git")
    if os.path.isdir(dot_git):
        git_dir = dot_git
    elif os.path.isfile(dot_git):
        with open(dot_git, "r", encoding="utf-8", errors="replace") as handle:
            text = handle.read().strip()
        if not text.startswith("gitdir:"):
            return []
        git_dir = os.path.join(repo, text[len("gitdir:"):].strip())
    elif os.path.isfile(os.path.join(repo, "HEAD")) and os.path.isdir(os.path.join(repo, "objects")):
        git_dir = repo
    else:
        return []
    found = [os.path.abspath(git_dir)]
    common = os.path.join(git_dir, "commondir")
    if os.path.isfile(common):
        with open(common, "r", encoding="utf-8", errors="replace") as handle:
            found.append(os.path.abspath(os.path.join(git_dir, handle.read().strip())))
    return found


def _rev_parse_lines(git, repo, args):
    """`git -C repo rev-parse <args>`'s output lines, or None when it fails or
    a line is empty (a path holding a newline then reads as a mismatch, which
    refuses)."""
    rc, out = _git(git, ["-C", repo, "rev-parse"] + args)
    if rc != 0:
        return None
    lines = out.decode("utf-8", "surrogateescape").split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines if all(lines) else None


def _directory_identity(path):
    """(st_dev, st_ino) of `path`, or its canonical spelling when it cannot be
    examined: two spellings of one directory (a symlink, a case-insensitive
    file system's other case) compare equal, two directories never do."""
    try:
        metadata = os.stat(path)
    except OSError:
        return ("unexamined", os.path.realpath(path))
    return (metadata.st_dev, metadata.st_ino)


def judge_git_layout(boundary, git, repo, place):
    """`repo` (the candidate, a --git-repo, a Cargo git database or checkout,
    or a repository nested in the work tree of one of them) must be
    what git itself uses when the gate (or Cargo) runs git there: a non-bare
    repository whose work-tree top
    is `repo` and whose git directories are the ones judge_all judged as
    trees (git_directories), or a bare repository that is `repo` itself.
    Otherwise git would read another repository's configuration, or run every
    configured program (a transport, credential helper, uploadpack, fsmonitor,
    hook) from a directory this check never judged as a tree: a
    core.worktree naming an ancestor or any other directory (git chdirs to
    it), a `repo` that is a subdirectory of a repository or holds no
    repository of its own (git searches its ancestors), a core.bare on a work
    tree's .git, a GIT_DIR or GIT_WORK_TREE (a submodule's own core.worktree,
    which names its work tree, passes: git reports that work tree as the
    top). Each refuses, fail closed (repair
    round 3 of OD-XHOST-TRANSPORT-WORDS-20261024). git is asked, not
    re-derived, because git's discovery and core.worktree decide its working
    directory; `rev-parse` runs no configured program. True when it
    passed."""
    expected = git_directories(repo)
    itself = _directory_identity(repo)
    remedy = ("remedy: point the variable at the repository's own top level, and unset core.worktree "
              "(`git -C <repo> config --unset core.worktree`; OD-XHOST-TRANSPORT-WORDS-20261024)")
    if not expected:
        boundary.refuse(repo, place, "holds no git repository of its own (no .git), so git run there searches "
                        "its ancestors for one and would use that repository's configuration and run its "
                        "configured programs from that repository's top level, which this check does not judge "
                        "as a tree; " + remedy)
        return False
    head = _rev_parse_lines(git, repo, ["--path-format=absolute", "--is-bare-repository", "--git-dir",
                                        "--git-common-dir"])
    if head is None or len(head) != 3 or head[0] not in ("true", "false") or not all(
            os.path.isabs(line) for line in head[1:]):
        boundary.refuse(repo, place, "`git rev-parse` could not report which repository git uses there, so this "
                        "check cannot judge where git runs its configured programs; " + remedy)
        return False
    reported = {_directory_identity(line) for line in head[1:]}
    judged = {_directory_identity(path) for path in expected}
    if reported != judged:
        boundary.refuse(repo, place, "git uses the git directory {} there, not {} that this check judged (a "
                        "GIT_DIR, or a .git or commondir file git reads differently), so its configuration and "
                        "hooks are not the ones judged; {}".format(
                            " and ".join(sorted(set(head[1:]))), " and ".join(sorted(set(expected))), remedy))
        return False
    if head[0] == "true":
        if _directory_identity(head[1]) != itself:
            boundary.refuse(repo, place, "git treats it as a bare repository whose git directory is {} "
                            "(core.bare on a work tree's .git), so git runs there from {}, not as the work tree "
                            "this check judged; {}".format(head[1], head[1], remedy))
            return False
        return True
    top = _rev_parse_lines(git, repo, ["--show-toplevel"])
    if top is None or len(top) != 1 or not os.path.isabs(top[0]):
        boundary.refuse(repo, place, "`git rev-parse --show-toplevel` could not report git's work tree there, so "
                        "this check cannot judge where git runs its configured programs; " + remedy)
        return False
    if _directory_identity(top[0]) != itself:
        boundary.refuse(repo, place, "git's work tree for it is {} (a core.worktree, or {} being a subdirectory "
                        "of that repository's work tree), so git runs the configured programs of a fetch, a "
                        "lazy fetch or a status (a transport, credential helper, uploadpack, fsmonitor, hook) from "
                        "{}, which this check does not judge as the work tree; {}".format(
                            top[0], repo, top[0], remedy))
        return False
    return True


def judge_alternates(boundary, git_dir, place):
    """Every object store git reads objects of `git_dir` from besides its own
    `objects`: each entry of `objects/info/alternates` (absolute, or relative
    to that objects directory, as git resolves it), then the alternates file
    of each store named, judged as whole trees (ruling LD-75). Refused: an
    alternates file that cannot be read, a C-quoted line (not parsed here),
    an entry that names no existing directory, an `info/http-alternates`
    file (stores named by URL), and more than ALTERNATES_LIMIT stores."""
    pending = [os.path.join(git_dir, "objects")]
    seen = set()
    while pending:
        objects = pending.pop()
        canonical = os.path.realpath(objects)
        if canonical in seen:
            continue
        seen.add(canonical)
        if len(seen) > ALTERNATES_LIMIT:
            boundary.refuse(objects, place, "chains more than {} alternate object stores".format(ALTERNATES_LIMIT))
            return
        info = os.path.join(canonical, "info")
        http = os.path.join(info, "http-alternates")
        if os.path.lexists(http):
            boundary.refuse(http, place, "names alternate object stores by URL, which this check cannot judge")
        alternates = os.path.join(info, "alternates")
        try:
            with open(alternates, "rb") as handle:
                data = handle.read()
        except (FileNotFoundError, NotADirectoryError):
            continue
        except OSError as error:
            boundary.refuse(alternates, place, "cannot be read ({})".format(error.strerror or error))
            continue
        for raw in data.split(b"\n"):
            if not raw or raw.startswith(b"#"):
                continue
            if raw.startswith(b'"'):
                boundary.refuse(alternates, place, "has a C-quoted line, which this check does not parse")
                break
            entry = os.fsdecode(raw)
            target = entry if os.path.isabs(entry) else os.path.join(canonical, entry)
            boundary.places.append("alternate object store {} (of {})".format(target, git_dir))
            boundary.judge_tree(target, place + ": an alternate object store")
            if not os.path.isdir(target):
                boundary.refuse(target, place, "is named in {} but is not a directory this check can read".format(
                    alternates))
                continue
            pending.append(target)


def _git_environment():
    """This environment for a git run, without the variables that make git
    read objects from another store (judge_all refuses them anyway)."""
    environment = {name: value for name, value in os.environ.items() if name not in GIT_OBJECT_STORE_VARIABLES}
    environment["GIT_TERMINAL_PROMPT"] = "0"
    return environment


def _git(git, args, cwd=None):
    """Run git (already judged) with this environment; (rc, stdout bytes)."""
    try:
        process = subprocess.Popen([git] + args, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, env=_git_environment())
        out, _ = process.communicate(timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None, b""
    return process.returncode, out


def _expand(value, base):
    """`value`, a path git reads (a configuration file's origin, core.hooksPath,
    core.attributesFile), as git resolves it: `~/` is HOME's and a relative
    path is relative to `base` (the work-tree top judge_git_layout verified).
    Not stripped: git's own parser already removed unquoted whitespace, and a
    quoted `"/x "` is the path `/x ` to git, so judging `/x` would judge
    another file (repair round 3)."""
    if value.startswith("~/"):
        value = os.path.join(os.environ.get("HOME", ""), value[2:])
    if value and not os.path.isabs(value):
        value = os.path.join(base, value)
    return value


def judge_named_path(boundary, word, label, place, search_path, program):
    """`word` names a path git or a program it starts uses: the PROGRAM
    (`program`) a command or variable names, or a path a later word of a git
    command key names. `~` or `~user` refuses (the shell expands it to a home
    directory); `~/` is HOME's (refused when HOME is not absolute); an
    absolute path is resolved and judged, and a later word's path that is a
    directory is judged as a whole tree (a program may run in it or search
    it; OD-XHOST-TRANSPORT-WORDS-20261024); a relative path with a slash
    refuses (git runs it from its working directory, and `../` can leave
    any judged tree; LD-75 repair); a bare program name is found on the
    judged PATH, as the shell and execvp find it, and that file is resolved
    too."""
    if word.startswith("~") and not word.startswith("~/"):
        # The shell expands `~` and `~user` to a home directory ($HOME, or
        # another account's), not a name found on PATH.
        boundary.refuse(label, place, "names {!r}, which the shell expands to a home directory (another account's "
                        "for `~user`), not a path this check resolves; remedy: name it by an absolute path or as "
                        "`~/...` (OD-XHOST-TRANSPORT-WORDS-20261024)".format(word))
        return
    if word.startswith("~/"):
        home = os.environ.get("HOME", "")
        if not os.path.isabs(home):
            boundary.refuse(label, place, "names {!r} below HOME, which is not an absolute path, so this check "
                            "cannot judge it (OD-XHOST-FETCH-TRANSPORT-20261016)".format(word))
            return
        word = os.path.join(home, word[2:])
    if os.path.isabs(word):
        target = boundary.resolve(word, place)
        if not program and target is not None and os.path.isdir(target):
            boundary.places.append("a directory {} names {}".format(label, target))
            boundary.judge_tree(target, place)
    elif "/" in word:
        if program:
            boundary.refuse(label, place, "names the program {!r} by a relative path, which git runs from its "
                            "working directory, so this check cannot judge it; remedy: name it by an absolute "
                            "path, or by a bare name found on PATH (LD-75)".format(word))
        else:
            boundary.refuse(label, place, "names the path {!r} by a relative path, which the program reads or "
                            "runs from git's working directory, so this check cannot judge it; remedy: name it "
                            "by an absolute path (OD-XHOST-FETCH-TRANSPORT-20261016)".format(word))
    elif program and word:
        found = shutil.which(word, path=search_path)
        if found:
            boundary.resolve(found, place)


def shell_words(value):
    """`value` split into words where the shell splits it (SHELL_WORD_SEPARATORS)."""
    return [word for word in SHELL_WORD_SEPARATORS.split(value) if word]


def shell_reserved(word):
    """Why `word`, the first word of a shell command, names no program this
    check can judge: a word the shell reads as reserved where a command
    begins (SHELL_RESERVED_WORDS), or a word that begins with `!`; else None
    (repair round 4 of OD-XHOST-TRANSPORT-WORDS-20261024)."""
    if word in SHELL_RESERVED_WORDS:
        return ("its first word {!r} is a word the shell reads as reserved where a command begins, not as a "
                "program, so the program it runs is a later word this check does not judge as one (`! /x` runs "
                "/x)".format(word))
    if word.startswith("!"):
        return ("its first word {!r} begins with `!`: git strips only one `!` (from an `alias.*` value or a "
                "credential helper, none from any other key), and the shell runs no program this check judges by "
                "that name (`!!/x` is the relative program `!/x` to the shell)".format(word))
    return None


def names_git(word):
    """Whether `word` names git as a program: `git`, or a path whose last
    component is `git`."""
    return os.path.basename(word) == "git"


def judge_transport_program(boundary, value, label, place, search_path, shell):
    """The program a fetch's transport runs, named by `value` (what `label`
    holds), judged as git runs it (OD-XHOST-TRANSPORT-WORDS-20261024, which
    supersedes the later-word rule of OD-XHOST-FETCH-TRANSPORT-20261016).
    Refused, as values this check cannot judge: an empty one; one holding a
    character the shell gives a meaning beyond separating words (SHELL_SYNTAX);
    for a shell command (`shell`), a first word that is an assignment (the
    shell would run the next word with a changed environment) or one the shell
    reads as reserved or that begins with `!` (`! ssh` runs ssh; repair round
    4); for a program
    git runs without a shell, any whitespace (git runs the whole value as one
    path). The program, the first word, is then judged by `judge_named_path`.
    For a shell command, ANY later word is then refused: git runs the command
    through the shell, so a later word can name, set or move where git's child
    finds a program or file (an option's value such as `-F config` or
    `-oProxyCommand=...`, `..`, an assignment), which this check does not
    parse; the remedy is ~/.ssh/config, which this check judges. Before
    this ruling only later words that this check recognized as a path, and only
    after a `=`, were judged, so `sh tools/evil=1`, `env PATH=tools evil-ssh`,
    `sh evil-ssh` and `ssh -F tools/config` passed (findings (2), (3) and (6))."""
    if not value.strip():
        why = "is empty, so this check cannot judge what git would run"
    elif SHELL_SYNTAX & set(value):
        why = "holds {}, which the shell gives a meaning this check does not parse, so it cannot judge what " \
              "git would run".format(" ".join(repr(character) for character in sorted(SHELL_SYNTAX & set(value))))
    elif shell and "=" in shell_words(value)[0]:
        why = "begins with the assignment {!r}, so the shell would run a later word with a changed " \
              "environment, which this check does not judge".format(shell_words(value)[0])
    elif shell and shell_reserved(shell_words(value)[0]):
        why = "is a shell command: {}".format(shell_reserved(shell_words(value)[0]))
    elif not shell and any(character.isspace() for character in value):
        why = "holds whitespace, but git runs the whole value as one program, which this check does not judge"
    else:
        why = None
    if why:
        boundary.refuse(label, place, "{}; {}".format(why, TRANSPORT_REMEDY))
        return
    words = shell_words(value) if shell else [value]
    judge_named_path(boundary, words[0], label, place, search_path, program=True)
    if shell and len(words) > 1:
        boundary.refuse(label, place, "runs the shell command {!r}, whose later word {!r} this check does not "
                        "judge: git runs it through the shell, so a later word can name, set or move where git's "
                        "child finds a program or file (an option's value, `..`, an assignment), which this check "
                        "does not parse; {}".format(
                            value, words[1], TRANSPORT_REMEDY))


def command_later_word(word):
    """One later word of a git command key's shell command, or any word of an
    `alias.*` value without `!` (repair round 4), read by its TEXT
    (OD-XHOST-TRANSPORT-WORDS-20261024, repair round 2): `(path, None)` when
    it names an absolute or `~/` path to judge (the whole word, or what
    follows the `=` of a plain `--option=`), `(None, None)` for a plain
    argument, `(None, why)` when it refuses. Refused: an environment
    assignment (`PATH=dir`, which changes what the command resolves); a word
    holding `..` (`../x`, `-C ..`, `-C..` name a directory above git's
    working directory); a word with a `/` or `~` that is not exactly such a
    path (an option's attached value `-S/x`, a relative path `tools/x`, a
    `~user` word the shell expands to another account's home, a `sed` script
    `s/a/b/`); a path holding a character a program may split a path list
    at or git or the shell may substitute in (PLAIN_PATH_TEXT); and a plain
    argument holding a character outside PLAIN_COMMAND_WORD. A plain
    argument's text names nothing outside git's working directory and PATH:
    as a name it resolves in git's working directory or on PATH, both judged
    (judge_all). What a program makes of a plain argument by its own rules (an
    option that selects a file or directory of the program's own choosing,
    such as a login shell's `-l` reading ~/.profile) is not judged here."""
    if ENVIRONMENT_ASSIGNMENT.match(word):
        return None, ("sets the environment, which can change which program or file the command resolves (a PATH it "
                      "sets, for instance)")
    if ".." in word:
        return None, ("holds `..`, which can name a directory above git's working directory (`../x`, `-C ..`, "
                      "`-C..`), outside what this check judges as git's working directory")
    if "/" not in word and "~" not in word:
        if PLAIN_COMMAND_WORD.fullmatch(word):
            return None, None
        return None, ("holds a character outside the plain-argument set [A-Za-z0-9_.,:@%+=-], which this check does "
                      "not interpret")
    if word.startswith(("/", "~/")):
        option, path = "", word
    elif "=" in word:
        option, path = word.split("=", 1)
    else:
        option, path = word, ""
    if not path.startswith(("/", "~/")) or (option and not PLAIN_COMMAND_WORD.fullmatch(option)):
        return None, ("holds a `/` or `~` but is neither an absolute or `~/` path nor a plain `--option=` followed "
                      "by one, so this check cannot take the path out of it (an option's attached value such as "
                      "`-S/x`, a relative path such as `tools/x`, a `~user` the shell expands to another account's "
                      "home, or a sed script such as `s/a/b/`)")
    if not PLAIN_PATH_TEXT.fullmatch(path[2:] if path.startswith("~/") else path):
        return None, ("names the path {!r}, which holds a character a program may split a path list at (`:` `,` `=`) "
                      "or that git or the shell may substitute in (`%` `~`), so this check cannot judge it as one "
                      "path".format(path))
    return path, None


def _bang_key(key):
    """Whether git strips one leading `!` from the value of `key` (lower case)
    and runs the rest as a shell command: an `alias.*` value and a credential
    helper (`credential.helper`, `credential.<url>.helper`). git strips none
    from any other key, so a leading `!` there stays part of the first word."""
    return key.startswith("alias.") or (key.startswith("credential.") and key.endswith(".helper"))


def judge_git_command_value(boundary, value, label, place, search_path, key):
    """The value of `key` (lower case), a git configuration key that runs a
    program (a filter, fsmonitor, credential helper, pager, editor,
    upload-pack, alias, ...), judged as git runs it
    (OD-XHOST-TRANSPORT-WORDS-20261024).

    Every value is a SHELL COMMAND, except an `alias.*` value without a
    leading `!` (below). git strips exactly one leading `!` from an alias and
    from a credential helper (`_bang_key`; tested on the value as git reads
    it, not after skipping blanks) and none from any other key. git runs a
    shell command through /bin/sh, so its program is its first word, split
    where the shell splits words: blanks and newlines, never str.strip()'s
    Unicode whitespace (`!<U+00A0>/x` is the RELATIVE program `<U+00A0>/x`;
    repair round 3). Refused: a shell metacharacter (the command is not
    parsed); a first word the shell reads as reserved, or that begins with
    `!` (`shell_reserved`: `!! /x` is `! /x` to the shell, which runs /x;
    a6cbba41b judged `!` as an unfound PATH name and passed it, while
    4a0668957 refused the value; repair round 4); a first word holding `=` (an
    environment assignment: `PATH=.. prog`, and the over-refused `LESS=FRX
    less`). The program is judged by `judge_named_path` (`~/` or absolute:
    resolved; a bare name: found on the judged PATH; a relative path with a
    slash, `~` and `~user`: refused) and every later word by
    `command_later_word` (an absolute or `~/` path resolved, a directory as a
    whole tree; a plain argument passes; anything else refuses).

    An `alias.*` value WITHOUT `!` is the list of arguments git runs itself
    after `git` (`git x a`, with `alias.x = fetch --upload-pack=/p`, runs `git
    fetch --upload-pack=/p a`), and git's options run programs
    (`--upload-pack=`, `-c core.sshCommand=`, `--exec-path=`). Its first word
    refuses by name when it is a git option (it begins with `-`: `-c`, `-C`,
    `--exec-path`, `--git-dir`, `--work-tree`, `--config-env`, ...); every
    word, the first included, is read by `command_later_word`; and the first
    word is judged as a program too, as 4a0668957 judged it.

    In both forms, a word naming git as a program (`names_git`: `git`, or a
    path whose last component is `git`) followed by a word that begins with
    `-` refuses by name: a git option there can make that git use a
    repository or configuration other than the ones judged (`git -C <dir>`,
    `--git-dir=<dir>`, `-c alias.x=...`), the alias's first-word rule for a
    git a command starts.

    Every alias is judged, whatever runs it: a command key can run git with
    an alias (`remote.origin.uploadpack = git x` makes the preflight's fetch
    run alias x from the Clean work tree: the round-3 verifier's B1 against
    a6cbba41b, which judged an alias's first word alone on the claim that the
    gate never runs an alias). This host's credential helper
    `!/usr/bin/gh auth git-credential` passes: no metacharacter, an absolute
    program, two plain arguments; so does `alias.st = status -s`."""
    bang = _bang_key(key) and value.startswith("!")
    if key.startswith("alias.") and not bang:
        judge_git_arguments(boundary, value, label, place, search_path)
        return
    command = (value[1:] if bang else value).strip(" \t\n")
    words = shell_words(command)
    program = words[0] if words else ""
    syntax = SHELL_SYNTAX & set(command)
    if syntax:
        boundary.refuse(label, place, "runs the shell command {!r}, which holds {}, a shell metacharacter this "
                        "check does not parse, so it cannot judge what git would run; {}".format(
                            command, " ".join(repr(character) for character in sorted(syntax)), GIT_COMMAND_REMEDY))
        return
    reserved = shell_reserved(program)
    if reserved:
        boundary.refuse(label, place, "runs the shell command {!r}: {}; {}".format(command, reserved,
                                                                                   GIT_COMMAND_REMEDY))
        return
    if "=" in program:
        boundary.refuse(label, place, "runs the shell command {!r}, which begins with the assignment {!r}, so the "
                        "shell would run the next word with a changed environment (a PATH it sets, for instance), "
                        "which this check does not judge; {}".format(command, program, GIT_COMMAND_REMEDY))
        return
    judge_named_path(boundary, program, label, place, search_path, program=True)
    for index, word in enumerate(words[1:], 1):
        why = _git_option_after_git(words, index - 1)
        if why:
            boundary.refuse(label, place, "runs the shell command {!r}, {}; {}".format(command, why,
                                                                                       GIT_COMMAND_REMEDY))
            return
        path, why = command_later_word(word)
        if why:
            boundary.refuse(label, place, "runs the shell command {!r}, whose later word {!r} {}, so this check "
                            "cannot judge what git would run; {}".format(command, word, why, GIT_COMMAND_REMEDY))
            return
        if path:
            judge_named_path(boundary, path, label, place, search_path, program=False)


def _git_option_after_git(words, index):
    """Why `words[index]` names git as a program and the next word is a git
    option (it begins with `-`), else None."""
    if index + 1 < len(words) and names_git(words[index]) and words[index + 1].startswith("-"):
        return ("whose word {!r} names git and is followed by the git option {!r}, which can make that git use a "
                "repository or configuration other than the ones this check judges (`-C <dir>`, `--git-dir=`, "
                "`-c alias.x=...`) or run a program its value names".format(words[index], words[index + 1]))
    return None


def judge_git_arguments(boundary, value, label, place, search_path):
    """An `alias.*` value without `!`: the arguments git runs itself after
    `git` (judge_git_command_value). Its first word refuses when it is a git
    option (begins with `-`); every word goes through `command_later_word`,
    and a word naming git followed by a git option refuses; the first word is
    also judged as a program (4a0668957's rule for every alias)."""
    words = shell_words(value)
    if not words:
        return
    if words[0].startswith("-"):
        boundary.refuse(label, place, "is the git argument list {!r}, whose first word {!r} is a git option "
                        "(`-c`, `-C`, `--exec-path`, `--git-dir`, `--work-tree`, `--config-env`, ...), which can "
                        "make git run a program its value names or use a repository or configuration other than "
                        "the ones this check judges; remedy: begin the alias with a git command, or make it a `!` "
                        "command that names a wrapper script by an absolute path "
                        "(OD-XHOST-TRANSPORT-WORDS-20261024)".format(value, words[0]))
        return
    for index, word in enumerate(words):
        why = _git_option_after_git(words, index - 1) if index else None
        if why:
            boundary.refuse(label, place, "is the git argument list {!r}, {}; {}".format(value, why,
                                                                                         GIT_COMMAND_REMEDY))
            return
        path, why = command_later_word(word)
        if why:
            boundary.refuse(label, place, "is the git argument list {!r}, whose word {!r} {}, so this check cannot "
                            "judge what git would run; {}".format(value, word, why, GIT_COMMAND_REMEDY))
            return
        if path:
            judge_named_path(boundary, path, label, place, search_path, program=False)
    judge_named_path(boundary, words[0], label, place, search_path, program=True)


def judge_git(boundary, search_path, repos, cargo_checkouts=()):
    """git's binary is a PATH command (judged there). Here: its exec path,
    the configuration files it reads for each repository, what that
    configuration names, and (OD-XHOST-GIT-PROGRAM-KEYS-20261024) every key of
    each repository's own configuration against the allowlist, the local
    repositories its remotes name, its submodule git directories'
    configuration, every repository nested in its work tree (a populated
    submodule of any layout included; judge_nested_repository), and the
    system and global keys the gate's own file carries (boundary.carried,
    which must be the same for every repository). `cargo_checkouts` (Cargo's
    git checkouts) get git's view of them (judge_git_layout) and their own
    configuration judged the same way."""
    git = shutil.which("git", path=search_path)
    if git is None or boundary.refusals:
        # No git, or a refusal already: run nothing.
        return
    xdg = os.environ.get("XDG_CONFIG_HOME") or os.path.join(os.environ.get("HOME", "/"), ".config")
    files = []
    for variable in ("GIT_CONFIG_SYSTEM", "GIT_CONFIG_GLOBAL"):
        if variable == "GIT_CONFIG_SYSTEM" and os.environ.get("GIT_CONFIG_NOSYSTEM"):
            continue
        rc, out = _git(git, ["var", variable])
        if rc == 0 and out.strip():
            files += [line for line in out.decode("utf-8", "replace").splitlines() if line]
        elif variable == "GIT_CONFIG_SYSTEM":
            files.append("/etc/gitconfig")
        elif os.environ.get("GIT_CONFIG_GLOBAL"):
            files.append(os.environ["GIT_CONFIG_GLOBAL"])
        else:
            files += [os.path.join(xdg, "git", "config"), os.path.join(os.environ.get("HOME", "/"), ".gitconfig")]
    files += [os.path.join(xdg, "git", "attributes"), os.path.join(xdg, "git", "ignore")]
    for path in files:
        boundary.places.append("git configuration {}".format(path))
        boundary.resolve(path, "git configuration")
    # Cargo's built-in libgit2 reads the default files itself (system, XDG,
    # ~/.gitconfig, with their includes) whatever GIT_CONFIG_GLOBAL,
    # GIT_CONFIG_SYSTEM and GIT_CONFIG_NOSYSTEM name, and runs the credential
    # helpers they configure: their keys are judged by the same rules even when
    # this environment points git elsewhere (repair round 2), so a caller's
    # GIT_CONFIG_GLOBAL cannot hide them. Nothing of them is carried.
    for path in (LIBGIT2_SYSTEM_CONFIG, os.path.join(xdg, "git", "config"),
                 os.path.join(os.environ.get("HOME", "/"), ".gitconfig")):
        if boundary.resolve(path, "git configuration Cargo's libgit2 reads") is None or not os.path.isfile(path):
            continue
        boundary.places.append("git configuration Cargo's libgit2 reads {}".format(path))
        listed = git_config_entries(git, config_file=path, scope="global", includes=True)
        if listed is None:
            boundary.refuse(path, "git configuration Cargo's libgit2 reads", "`git config --file --includes "
                            "--list` cannot list it")
            continue
        judge_config_entries(boundary, git, path, listed, search_path, origin_base=os.path.dirname(path))
    rc, out = _git(git, ["--exec-path"])
    if rc == 0 and out.strip():
        boundary.places.append("git exec path {}".format(out.decode().strip()))
        boundary.judge_tree(out.decode("utf-8", "replace").strip(), "git exec path")
    for repo in repos:
        # A missing directory: `git -C` fails there and runs nothing (judge_all
        # judged that no other user can create it).
        if not os.path.isdir(repo):
            continue
        if boundary.refusals:
            return
        # git's own view of the repository first: a subdirectory, a missing
        # .git or a core.worktree would make git use a configuration or a
        # working directory other than the ones judged (repair round 3).
        if not judge_git_layout(boundary, git, repo, "the git repository {}".format(repo)):
            continue
        carried = judge_repository_configuration(boundary, git, repo, search_path)
        if carried is None:
            continue
        if boundary.carried is None:
            boundary.carried = carried
        elif carried != boundary.carried:
            # A conditional include (includeIf gitdir:/onbranch:) gives this
            # repository other system/global keys than the first one: the
            # gate's one configuration file cannot carry both.
            boundary.refuse(repo, "git configuration of {}".format(repo), "is given other carried system or global "
                            "keys (credential helpers, identity, core.excludesFile) than {} (a conditional include?), "
                            "so the run's one git configuration cannot carry them; remedy: make them the same for "
                            "every repository (OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(repos[0]))
    for checkout in cargo_checkouts:
        if boundary.refusals:
            return
        # git's own view first, as for a --git-repo: a core.worktree naming
        # another directory would make a git started there run from a
        # directory this check did not judge as the checkout (repair round 2).
        place = "the Cargo git checkout {}".format(checkout)
        if judge_git_layout(boundary, git, checkout, place):
            judge_repository_configuration(boundary, git, checkout, search_path, local_only=True)


class ConfigEntry:
    """One key of `git config --list --show-scope --show-origin -z`: its scope,
    origin, key as git prints it (section and name in lower case, a
    subsection as written), lower-case key, value (None for a key with no
    value) and the value's raw bytes."""

    def __init__(self, scope, origin, raw_key, value, raw_value):
        self.scope = scope
        self.origin = origin
        self.raw_key = raw_key
        self.key = raw_key.lower()
        self.value = value
        self.raw_value = raw_value


def git_config_entries(git, repo=None, config_file=None, scope=None, includes=False):
    """The configuration git reads in `repo` (or the one file `config_file`,
    every key then given `scope`, its includes followed with `includes`), or
    None when git cannot list it."""
    args = (["-C", repo] if repo else []) + ["config"] + (["--file", config_file] if config_file else []) + (
        ["--includes"] if includes else []) + ["--list", "--show-scope", "--show-origin", "-z"]
    rc, out = _git(git, args)
    if rc != 0:
        return None
    fields = out.split(b"\0")
    entries = []
    for index in range(0, len(fields) - 2, 3):
        raw_key, separator, raw_value = fields[index + 2].partition(b"\n")
        entries.append(ConfigEntry(scope or fields[index].decode("utf-8", "replace"),
                                   fields[index + 1].decode("utf-8", "replace"), raw_key.decode("utf-8", "replace"),
                                   raw_value.decode("utf-8", "replace") if separator else None,
                                   raw_value if separator else None))
    return entries


def split_config_key(key):
    """(section, subsection or None, name) of a key as git prints it: the
    section is up to the first dot and the name after the last one."""
    section, _, rest = key.partition(".")
    if "." not in rest:
        return section, None, rest
    subsection, _, name = rest.rpartition(".")
    return section, subsection, name


def local_key_allowed(key):
    """Whether the lower-case `key` may appear in a repository's own
    configuration (OD-XHOST-GIT-PROGRAM-KEYS-20261024)."""
    if key in LOCAL_DATA_KEYS or key in LOCAL_JUDGED_PATH_KEYS:
        return True
    section, subsection, name = split_config_key(key)
    if subsection is None:
        return section in LOCAL_DATA_SECTIONS
    return name in LOCAL_DATA_SECTION_KEYS.get(section, ())


def carried_key(key):
    """Whether the gate's git configuration carries the lower-case system or
    global `key` (CARRIED_KEYS, CARRIED_CREDENTIAL_NAMES)."""
    section, _subsection, name = split_config_key(key)
    return key in CARRIED_KEYS or (section == "credential" and name in CARRIED_CREDENTIAL_NAMES)


def remote_url_local_path(url):
    """(path, why) for a remote's location as git reads it: path is the local
    path it names ('' for a network URL, an scp-like ssh location or a remote
    helper other than ext::), why a refusal reason. git reads a location with
    no `:` before its first `/` as a local path (connect.c
    url_is_local_not_ssh), percent-decodes a file:// URL, and resolves a
    relative path in its working directory."""
    if not url:
        return None, "is empty"
    helper = re.match(r"([A-Za-z0-9][A-Za-z0-9+.-]*)::", url)
    if helper and "://" not in url[:helper.end()]:
        if helper.group(1).lower() == "ext":
            return None, "is an ext:: location, which names a command git runs"
        return "", None
    if "://" in url:
        if url.split("://", 1)[0].lower() != "file":
            return "", None
        path = url[len("file://"):]
        if "%" in path or not path.startswith("/"):
            return None, "is a file:// URL that is not a plain absolute path (git percent-decodes it)"
        return path, None
    colon, slash = url.find(":"), url.find("/")
    if colon >= 0 and not (0 <= slash < colon):
        return "", None
    if not url.startswith("/"):
        return None, "names a repository by a relative or `~` path, which git resolves from its working directory"
    return url, None


def judge_local_remote(boundary, git, url, label, place, search_path):
    """A remote location `url` (the value of `label`) that names a local
    repository: git runs upload-pack there with that repository's own
    configuration, so it is judged as a repository the run uses git in (its
    tree, git directories, alternates and local configuration), once per
    repository ("local remote" of REPOSITORY_JUDGEMENTS). upload-pack uses no
    work tree, so git's view of one is not asked here; a local remote that git
    also enters as a work tree (a populated submodule) is given that
    judgement where it is reached as one, whichever comes first. A path that
    is not a directory holding a repository refuses (git would also try
    `<path>.git`)."""
    path, why = remote_url_local_path(url)
    if why:
        boundary.refuse(label, place, "{}, so this check cannot judge the repository git would run upload-pack in; "
                        "remedy: name the remote by a network URL or an absolute path "
                        "(OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(why))
        return
    if not path:
        return
    canonical = boundary.resolve(path, place)
    directories = git_directories(canonical) if canonical is not None and os.path.isdir(canonical) else []
    if not directories:
        boundary.refuse(label, place, "names {!r}, which is not a directory holding a git repository this check "
                        "can judge (git would look for {!r} too); remedy: name an existing repository by its "
                        "absolute path (OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(path, path + ".git"))
        return
    if not boundary.first_judgement(canonical, "local remote"):
        return
    what = "the local repository {} names".format(label)
    boundary.places.append("{} {}".format(what, canonical))
    boundary.judge_tree(canonical, place + ": " + what)
    for git_dir in directories:
        boundary.judge_tree(git_dir, place + ": " + what)
        judge_alternates(boundary, git_dir, place + ": " + what)
    judge_repository_configuration(boundary, git, canonical, search_path, local_only=True)


def submodule_git_directories(git_dir):
    """Every submodule git directory below `git_dir`/modules (nested ones
    included): a directory holding HEAD and config. git runs in each when a
    status descends into a populated submodule."""
    found, seen = [], set()
    pending = [os.path.join(git_dir, "modules")]
    while pending:
        directory = pending.pop()
        canonical = os.path.realpath(directory)
        if canonical in seen or not os.path.isdir(canonical):
            continue
        seen.add(canonical)
        try:
            names = sorted(os.listdir(canonical))
        except OSError:
            continue
        if "HEAD" in names and "config" in names:
            found.append(canonical)
            pending.append(os.path.join(canonical, "modules"))
            continue
        pending += [os.path.join(canonical, name) for name in names]
    return found


def judge_legacy_remotes(boundary, git_dir, place):
    """A file below `git_dir`'s remotes/ or branches/ defines a remote outside
    the configuration (git reads `$GIT_COMMON_DIR/remotes/<name>` and
    `branches/<name>` for a remote name the configuration does not define),
    so its URL is a location this check never judges: refused. An empty or
    missing directory passes (`git init`'s template creates an empty
    branches/)."""
    for name in ("remotes", "branches"):
        directory = os.path.join(git_dir, name)
        try:
            entries = sorted(os.listdir(directory))
        except (FileNotFoundError, NotADirectoryError):
            continue
        except OSError as error:
            boundary.refuse(directory, place, "cannot be listed ({})".format(error.strerror or error))
            continue
        if entries:
            boundary.refuse(directory, place, "defines the remote(s) {} outside the configuration (git reads such a "
                            "file for a remote name the configuration does not define), so the location git would "
                            "fetch from is one this check does not judge; remedy: define the remote in the "
                            "repository's configuration (`git remote add`) and remove the file "
                            "(OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(", ".join(entries)))


def repository_work_tree(boundary, git, repo, place):
    """The work-tree top git reports for `repo` (absolute, as git spells it),
    '' when git uses no work tree there (a bare repository, or a git
    directory), or None after a refusal."""
    inside = _rev_parse_lines(git, repo, ["--is-inside-work-tree"])
    if inside is None or len(inside) != 1 or inside[0] not in ("true", "false"):
        boundary.refuse(repo, place, "`git rev-parse --is-inside-work-tree` failed there, so this check cannot "
                        "find the repositories git would enter below it")
        return None
    if inside[0] == "false":
        return ""
    top = _rev_parse_lines(git, repo, ["--show-toplevel"])
    if top is None or len(top) != 1 or not os.path.isabs(top[0]):
        boundary.refuse(repo, place, "`git rev-parse --show-toplevel` could not report git's work tree there, so "
                        "this check cannot find the repositories git would enter below it")
        return None
    return top[0]


def nested_repositories(boundary, git, top, place):
    """Every repository nested in the work tree `top` (canonical), as
    directories, or None after a refusal (repair round 2 of
    OD-XHOST-GIT-PROGRAM-KEYS-20261024):

    * every directory below `top` that holds an entry named `.git` (a
      directory, a `gitdir:` file or a symlink), as judge_tree's walk of the
      tree recorded them (Boundary.git_holders; `top` is walked first if no
      judged tree covers it), outside any `.git` directory: a populated
      submodule of every layout (its git directory absorbed below
      <git-dir>/modules, embedded in the path as a plain clone or Cargo's
      checkout submodules leave it, or a `gitdir:` file naming any
      directory), a Lake package, an untracked or ignored clone;
    * the work-tree path of every gitlink (mode 160000) of the index whose
      path holds a `.git`, read with `git ls-files --stage -z` with
      core.fsmonitor off on the command line (the listing runs no configured
      program; the repository's own configuration was judged already). This
      adds a gitlink path that is a symlink to a directory elsewhere: git
      status follows it (`cd <path>; GIT_DIR=.git git status`, measured with
      git 2.43), and the walk does not.

    git status runs git in each populated submodule with that repository's
    own configuration; git run in any other of them (Lake's, or a judged
    program's `env -C <word> git`) does too."""
    boundary.judge_tree(top, place)
    if boundary.refusals:
        return None
    prefix = top.rstrip(os.sep) + os.sep
    found = []
    for holder in sorted(boundary.git_holders):
        if holder.startswith(prefix) and ".git" not in holder[len(prefix):].split(os.sep):
            found.append(holder)
    rc, out = _git(git, ["-C", top, "-c", "core.fsmonitor=false", "ls-files", "--stage", "-z"])
    if rc != 0:
        boundary.refuse(top, place, "`git ls-files --stage` failed there, so this check cannot list the submodules "
                        "git status descends into")
        return None
    for record in out.split(b"\0"):
        if not record:
            continue
        meta, tab, name = record.partition(b"\t")
        if not tab:
            boundary.refuse(top, place, "`git ls-files --stage` printed a record this check cannot read")
            return None
        if meta.split(b" ", 1)[0] != b"160000":
            continue
        path = os.path.join(top, os.fsdecode(name))
        if os.path.lexists(os.path.join(path, ".git")) and path not in found:
            found.append(path)
    return found


def judge_nested_repository(boundary, git, path, search_path, outer):
    """A repository nested in the work tree of `outer` (nested_repositories):
    git status runs git in it when it is a populated submodule, with its own
    configuration, so it is judged as a repository the run uses git in: its
    path resolved hop by hop, its work tree and git directories as trees
    (with alternates), git's own view of it (judge_git_layout: its work-tree
    top must be `path` itself, so a core.worktree naming any other directory
    refuses), and its configuration against the allowlist with the
    repositories nested in it in turn (judge_repository_configuration). A
    `.git` git cannot use as a repository refuses. Made once per repository
    ("nested repository" of REPOSITORY_JUDGEMENTS), whatever judgement of it
    was made first: a repository a local remote names, whose configuration
    was judged without git's view of its work tree, is still judged here in
    full (repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024)."""
    place = "the repository {} nested in {}".format(path, outer)
    canonical = boundary.resolve(path, place)
    if canonical is None or not os.path.isdir(canonical):
        boundary.refuse(path, place, "holds a .git but does not resolve to a directory this check can judge")
        return
    if not boundary.first_judgement(canonical, "nested repository"):
        return
    boundary.places.append(place)
    boundary.judge_tree(canonical, place)
    directories = git_directories(canonical)
    if not directories:
        boundary.refuse(os.path.join(canonical, ".git"), place, "is a .git this check cannot read as a repository "
                        "(not a git directory, nor a `gitdir:` file), so it cannot judge the configuration git "
                        "would use there; remedy: remove it or make it a repository "
                        "(OD-XHOST-GIT-PROGRAM-KEYS-20261024)")
        return
    for git_dir in directories:
        boundary.judge_tree(git_dir, place + ": its git directory")
        judge_alternates(boundary, git_dir, place + ": its git directory")
    if boundary.refusals:
        return
    if judge_git_layout(boundary, git, canonical, place):
        judge_repository_configuration(boundary, git, canonical, search_path, local_only=True)


def judge_repository_configuration(boundary, git, repo, search_path, local_only=False):
    """Judge the configuration git reads in `repo`, every key of every scope
    by judge_config_entries, then each submodule git directory's config (and
    config.worktree) below <git-dir>/modules as a local scope, the legacy
    remote files of each git directory (judge_legacy_remotes), and then
    every repository nested in its work tree (nested_repositories,
    judge_nested_repository; once per repository, recursively). With
    `local_only` only the local and worktree scopes are judged (a repository
    whose system and global keys are the run's own file or were judged
    already). Returns the carried system and global keys, or None when the
    configuration could not be listed. With `local_only`, a repository whose
    configuration was judged already ("configuration" or "local
    configuration" of REPOSITORY_JUDGEMENTS) is not judged again (its local
    scopes were judged; [] is returned); a full judgement is always made.
    The nested walk is made once per repository ("nested walk"), whichever
    judgement reached it first. Neither stands in for git's view of the work
    tree (judge_git_layout), which each caller that needs it asks itself."""
    place = "git configuration of {}".format(repo)
    carried = []
    if not (local_only and (boundary.has_judgement(repo, "configuration")
                            or boundary.has_judgement(repo, "local configuration"))):
        boundary.first_judgement(repo, "local configuration" if local_only else "configuration")
        entries = git_config_entries(git, repo)
        if entries is None:
            boundary.refuse(repo, "git configuration", "`git config --list --show-scope --show-origin` failed")
            return None
        carried = judge_config_entries(boundary, git, repo, entries, search_path, local_only)
        for git_dir in git_directories(repo):
            judge_legacy_remotes(boundary, git_dir, place)
            for module in submodule_git_directories(git_dir):
                judge_legacy_remotes(boundary, module, place)
                for name in ("config", "config.worktree"):
                    path = os.path.join(module, name)
                    if not os.path.isfile(path):
                        continue
                    listed = git_config_entries(git, config_file=path, scope="local")
                    if listed is None:
                        boundary.refuse(path, place, "`git config --file` cannot list this submodule "
                                        "configuration")
                        continue
                    judge_config_entries(boundary, git, module, listed, search_path, True,
                                         origin_base=os.path.dirname(path))
    if boundary.refusals:
        # Nothing more runs in a repository whose configuration refused.
        return carried
    if not boundary.first_judgement(repo, "nested walk"):
        return carried
    top = repository_work_tree(boundary, git, repo, place)
    if not top:
        return carried
    nested = nested_repositories(boundary, git, _canonical(boundary, top, place), place)
    for path in nested or ():
        if boundary.refusals:
            break
        judge_nested_repository(boundary, git, path, search_path, repo)
    return carried


def judge_config_entries(boundary, git, repo, entries, search_path, local_only=False, origin_base=None):
    """The keys `entries` of `repo`'s configuration, as git runs and reads them.
    Every key: the file it comes from is judged; the program and path rules
    of judge_git (command keys, transport keys, paths); a remote.*.uploadpack
    or .receivepack refuses outright in every scope (git passes a local
    remote's path to it as its last argument; R2 of
    OD-XHOST-GIT-PROGRAM-KEYS-20261024); a credential helper with no value or
    with a later word naming a directory refuses (a program it starts could
    run there). A local or worktree key must be on the allowlist
    (local_key_allowed), and a remote location naming a local repository is
    judged as a repository (judge_local_remote). A local branch.<name>.remote,
    branch.<name>.pushRemote or remote.pushDefault naming neither `.` (the
    repository itself) nor a remote whose url this configuration sets is a
    location git would use as given (a relative name is a path in git's
    working directory), so it is judged as a remote location
    (judge_local_remote: a relative one refuses). Returns the system and
    global entries the gate's file carries, as (raw key, raw value) pairs in
    order."""
    carried = []
    configured_remotes = set()
    for entry in entries:
        section, subsection, name = split_config_key(entry.raw_key)
        if (entry.scope in LOCAL_CONFIG_SCOPES and section.lower() == "remote" and subsection is not None
                and name.lower() == "url"):
            configured_remotes.add(subsection)
    for entry in entries:
        local = entry.scope in LOCAL_CONFIG_SCOPES
        if local_only and not local:
            continue
        key, value = entry.key, entry.value
        separator = value is not None
        value = value if separator else ""
        label = "{} {}".format(repo, key)
        place = "git configuration of {}: {}".format(repo, key)
        base_place = "git configuration of {}".format(repo)
        if entry.origin.startswith("file:"):
            boundary.resolve(_expand(entry.origin[len("file:"):], origin_base or repo), base_place)
        judge_config_key(boundary, repo, key, value, separator, search_path)
        section, subsection, name = split_config_key(key)
        if section == "remote" and subsection is not None and name in ("uploadpack", "receivepack"):
            boundary.refuse(label, place, "names the program git runs for a fetch or push from that remote; git "
                            "passes the remote's path to it as its last argument, so a local remote's location "
                            "becomes a word this check cannot judge; refused outright in every scope; " +
                            LOCAL_KEY_REMEDY)
        if section == "credential" and name == "helper":
            judge_credential_helper(boundary, value, separator, label, place)
        if local and not local_key_allowed(key):
            boundary.refuse(label, place, "is a key of the repository's own ({}) configuration that is not on the "
                            "allowlist of keys that name no program (data keys, and core.hooksPath, "
                            "core.excludesFile, core.attributesFile, core.worktree and core.sharedRepository, "
                            "which are judged); a key this check does not list may name a program a git helper "
                            "or extension runs; {}".format(entry.scope, LOCAL_KEY_REMEDY))
        if section in REMOTE_URL_NAMES and subsection is not None and name in REMOTE_URL_NAMES[section]:
            judge_local_remote(boundary, git, value, label, place, search_path)
        if local and ((section == "branch" and subsection is not None and name in
                                     ("remote", "pushremote")) or key == "remote.pushdefault"):
            if value != "." and value not in configured_remotes:
                judge_local_remote(boundary, git, value, label, place, search_path)
        if not local and carried_key(key):
            carried.append((entry.raw_key, entry.raw_value))
    return carried


def judge_credential_helper(boundary, value, separator, label, place):
    """A credential helper is the one configured program the run's own git
    runs (the gate's file carries it; Cargo's libgit2 reads it from the
    user's files itself). Beyond judge_git_command_value: a helper with no
    value refuses (git rejects it), and a later word naming an existing
    directory refuses, since a program given a directory can start git
    there, in a repository whose configuration this check did not judge
    (`env -C <dir> git ...`; OD-XHOST-GIT-PROGRAM-KEYS-20261024)."""
    if not separator:
        boundary.refuse(label, place, "has no value, which git rejects; remedy: give it a value or remove it")
        return
    command = value[1:] if value.startswith("!") else value
    for word in shell_words(command)[1:]:
        path, _ = command_later_word(word)
        if path is None:
            continue
        if path.startswith("~/"):
            path = os.path.join(os.environ.get("HOME", ""), path[2:])
        if os.path.isdir(path):
            boundary.refuse(label, place, "runs {!r}, whose later word {!r} names the directory {}, where a program "
                            "it starts could run git with a configuration this check did not judge; remedy: name "
                            "files only (OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(value, word, path))
            return


def judge_config_key(boundary, repo, key, value, separator, search_path):
    """One configuration key's program and path rules (unchanged from repair
    round 4 of OD-XHOST-TRANSPORT-WORDS-20261024)."""
    place = "git configuration of {}".format(repo)
    if key == "core.sharedrepository" and not (separator and value.strip().lower() in GIT_UMASK_SHARING):
        # git then sets the modes of what it writes in the repository
        # (the attestation's objects and refs, a worktree's metadata)
        # itself, past the umask 077 an --attest run relies on (LD-75).
        boundary.refuse("{} core.sharedRepository".format(repo), place, "is {!r}: git would set the modes "
                        "of what it writes there past the run's umask 077 (only `umask` or `false` "
                        "passes; LD-75)".format(value if separator else "(no value: group)"))
    elif key == "core.hookspath":
        boundary.judge_tree(_expand(value, repo), place + ": core.hooksPath")
    elif key in ("core.attributesfile", "core.excludesfile"):
        boundary.resolve(_expand(value, repo), place + ": " + key)
    elif key in TRANSPORT_KEYS:
        # core.gitProxy's ` for <domain>` limits it to a domain;
        # the command is what precedes it.
        command = value.split(" for ", 1)[0] if key == "core.gitproxy" else value
        judge_transport_program(boundary, command if separator else "", "{} {}".format(repo, key),
                                place + ": " + key, search_path, TRANSPORT_KEYS[key])
    elif key in EXT_PROTOCOL_KEYS:
        if not (separator and value.strip().lower() == "never"):
            boundary.refuse("{} {}".format(repo, key), place, "is {!r}, which can let git's ext:: transport "
                            "run the command a remote URL names, which this check does not judge; only "
                            "`never` passes (OD-XHOST-FETCH-TRANSPORT-20261016)".format(
                                value if separator else "(no value)"))
    elif key in GIT_COMMAND_KEYS or key.endswith(GIT_COMMAND_KEY_SUFFIXES) or key.startswith("alias."):
        judge_git_command_value(boundary, value if separator else "", "{} {}".format(repo, key),
                                place + ": " + key, search_path, key)


# What a python3 run WITHOUT -I adds to the import path at startup beyond the
# `-I` path judge_all judges as this check's own sys.path (site.py's
# addusersitepackages, as CPython 3.9 to 3.13 read it): python3's user
# site-packages; for each `.pth` file there (the names that do not start with
# ".", in sorted order), every directory a path line names (joined to the
# site directory and made absolute), appended to sys.path, and every line
# that starts with "import " or "import\t", executed; then a sitecustomize
# and a usercustomize module, imported from the resulting path. Every python3
# the gate scripts start runs with -I, so this is the path of a python3 a leg
# starts (the bridge tests' report scripts, for instance).
PTH_EXECUTED_PREFIXES = ("import ", "import\t")
STARTUP_MODULES = ("sitecustomize", "usercustomize")
PTH_PLACE = "a .pth file of python3's user site-packages"
# The characters str.splitlines splits a line at besides \n and \r (and so
# \r\n): CPython 3.13's site.addpackage reads a .pth file's lines with
# str.splitlines (gh-117802), CPython 3.12 and earlier with universal
# newlines (\n, \r, \r\n only), so a .pth holding one is read as different
# lines by different python3 versions, and a path line under one splitting
# can hold an `import` line under the other. A unit test re-derives this set
# from str.splitlines over every code point. judge_user_site refuses a .pth
# holding any of them (repair round 3 of OD-XHOST-GATE-CWD-20261025); the
# three outside ASCII are refused before, as non-ASCII.
PTH_OTHER_LINE_SEPARATORS = frozenset("\x0b\x0c\x1c\x1d\x1e\x85\u2028\u2029")


def judge_user_site(boundary, user_site):
    """The import path a python3 run without -I gets from the user
    site-packages `user_site` (judged as a tree by the caller), judged
    without running any of it (OD-XHOST-GATE-CWD-20261025, repair round 2):
    every directory a `.pth` path line there names, as a tree, whether it
    exists yet or not; and refused outright, because what it does at every
    such start can be judged only by running it: a `.pth` line python3
    executes, and a sitecustomize or usercustomize module in the user
    site-packages or in a directory a `.pth` file names. A `.pth` file is
    read as python3 reads it: line by line with universal newlines, a line
    starting with `#` or blank skipped, a path line stripped at its end only.
    One that is not a regular file python3 can read, holds a byte outside
    ASCII (python3 decodes it by the locale) or holds a character
    str.splitlines splits a line at other than \\n and \\r
    (PTH_OTHER_LINE_SEPARATORS: python3 3.13 splits its lines there, 3.12
    does not) refuses, rather than being judged under both splittings: no
    python3 that reads it is then certain to read the lines judged here, and
    no .pth file a tool writes holds one (repair round 3)."""
    if not user_site or not os.path.isabs(user_site):
        return  # judge_tree refused a root that is not absolute
    try:
        names = sorted(os.listdir(user_site))
    except (FileNotFoundError, NotADirectoryError):
        return
    except OSError as error:
        boundary.refuse(user_site, "python3's user site-packages", "cannot be listed ({})".format(
            error.strerror or error))
        return
    directories = [user_site]
    for name in names:
        if not name.endswith(".pth") or name.startswith("."):
            continue
        path = os.path.join(user_site, name)
        try:
            metadata = os.stat(path)
        except FileNotFoundError:
            continue
        except OSError as error:
            boundary.refuse(path, PTH_PLACE, "cannot be examined ({})".format(error.strerror or error))
            continue
        if stat.S_ISDIR(metadata.st_mode):
            continue  # python3's open of a directory fails, and it reads nothing
        if not stat.S_ISREG(metadata.st_mode):
            boundary.refuse(path, PTH_PLACE, "is not a regular file, so this check cannot read it as python3 "
                            "would at the start of every run without -I; remedy: remove it "
                            "(OD-XHOST-GATE-CWD-20261025)")
            continue
        try:
            with open(path, "rb") as handle:
                data = handle.read()
        except OSError as error:
            boundary.refuse(path, PTH_PLACE, "cannot be read ({})".format(error.strerror or error))
            continue
        try:
            text = data.decode("ascii")
        except UnicodeDecodeError:
            boundary.refuse(path, PTH_PLACE, "holds a byte outside ASCII, which python3 decodes by its locale, so "
                            "this check cannot tell which directories it names; remedy: remove the file or name "
                            "its directories in ASCII (OD-XHOST-GATE-CWD-20261025)")
            continue
        separators = sorted(PTH_OTHER_LINE_SEPARATORS.intersection(text))
        if separators:
            boundary.refuse(path, PTH_PLACE, "holds {}, which python3 3.13 reads as a line break (str.splitlines) "
                            "and 3.12 and earlier do not, so this check cannot tell which lines python3 reads from it "
                            "at the start of every run without -I; remedy: remove the file, or break its lines with "
                            "\\n only (OD-XHOST-GATE-CWD-20261025)".format(
                                ", ".join("U+{:04X}".format(ord(character)) for character in separators)))
            continue
        for number, line in enumerate(io.StringIO(text, newline=None), 1):
            if line.startswith("#") or line.strip() == "":
                continue
            if line.startswith(PTH_EXECUTED_PREFIXES):
                boundary.refuse(path, PTH_PLACE, "line {} is code python3 executes at the start of every run "
                                "without -I (a leg's python3), which can put entries on its import path or install "
                                "import hooks this check can judge only by running it; remedy: remove the line or "
                                "the file, or install that package outside the user site-packages, in a virtual "
                                "environment (OD-XHOST-GATE-CWD-20261025)".format(number))
                break
            directory = os.path.abspath(os.path.join(user_site, line.rstrip()))
            what = "a directory {} names".format(path)
            boundary.places.append("{} {}".format(what, directory))
            boundary.judge_tree(directory, what)
            directories.append(directory)
    for directory in directories:
        try:
            entries = sorted(os.listdir(directory))
        except OSError:
            continue  # missing, or refused by its judge_tree
        for entry in entries:
            if entry.split(".", 1)[0] in STARTUP_MODULES:
                boundary.refuse(os.path.join(directory, entry), "a module python3 imports at startup",
                                "is a {} module on the import path of a python3 run without -I (a leg's), which "
                                "imports and runs it at the start of every such run; what it does there can be "
                                "judged only by running it; remedy: remove it (OD-XHOST-GATE-CWD-20261025)".format(
                                    entry.split(".", 1)[0]))


PINNED_PYTHON3_PLACE = "the gate's pinned python3 (SOUNDNESS_PYTHON3)"
PINNED_PYTHON3_REMEDY = ("remedy: run scripts/soundness_check.sh --attest as a script file, with SOUNDNESS_PYTHON3 "
                         "unset, so that it pins the python3 its PATH finds (OD-XHOST-GATE-CWD-20261025)")


def judge_pinned_python3(boundary, pinned):
    """The gate's pinned interpreter, `pinned` (soundness_check.sh's
    SOUNDNESS_PYTHON3; repair round 3 of OD-XHOST-GATE-CWD-20261025): every
    python3 the gate and its helpers start is this one file, resolved before
    the gate_env.sh prelude put $HOME/.elan/bin first on PATH. It must be a
    canonical absolute path; it is judged with every directory it is looked up
    in (resolve), and so is each pyvenv.cfg python3 would read for it
    (judge_venv_configurations); and it must be the interpreter running this
    check, by canonical path (the realpath of the executable python3 names
    as its own) and by device and inode, so the interpreter and import path
    this check judges as its own are what the gate runs. That executable name
    is what python3 derives from its argv[0], which the program that started
    it chose (`exec -a`), so it must also be no script (a `#!` file: the
    kernel ran its interpreter instead) and, where /proc/self/exe names the
    program the kernel runs (Linux), that very file by device and inode
    (repair round 4). Each failure refuses."""
    if not pinned or not os.path.isabs(pinned):
        boundary.refuse(pinned or "(empty)", PINNED_PYTHON3_PLACE, "is not an absolute path; " + PINNED_PYTHON3_REMEDY)
        return
    canonical = os.path.realpath(pinned)
    if canonical != pinned:
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "is not a canonical path (it resolves to {}), so the file the "
                        "gate starts by that name is not certainly the one judged here; {}".format(
                            canonical, PINNED_PYTHON3_REMEDY))
        return
    boundary.places.append("{} {}".format(PINNED_PYTHON3_PLACE, pinned))
    if boundary.resolve(pinned, PINNED_PYTHON3_PLACE) is None:
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "does not exist; " + PINNED_PYTHON3_REMEDY)
        return
    executable = sys.executable
    running = os.path.realpath(executable) if executable and os.path.isabs(executable) else ""
    try:
        pinned_metadata = os.stat(pinned)
        running_metadata = os.stat(running) if running else None
    except OSError as error:
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "cannot be examined ({})".format(error.strerror or error))
        return
    if running != pinned or running_metadata is None or (pinned_metadata.st_dev, pinned_metadata.st_ino) != (
            running_metadata.st_dev, running_metadata.st_ino):
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "is not the interpreter running this check ({}), so what this "
                        "check judged as its own interpreter and import path is not what the gate runs; {}".format(
                            running or "it names no executable by an absolute path", PINNED_PYTHON3_REMEDY))
        return
    # The executable python3 names as its own is the file it derives from its
    # argv[0]: a wrapper that runs another binary under its own name (`exec
    # -a "$0" /elsewhere/python3.12`) makes it name the wrapper, and every
    # python3 the gate starts by the pin then runs a binary this check never
    # judged (repair round 4 of OD-XHOST-GATE-CWD-20261025).
    try:
        with open(pinned, "rb") as handle:
            head = handle.read(2)
    except OSError as error:
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "cannot be read ({})".format(error.strerror or error))
        return
    if head == b"#!":
        boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "is a script (it begins with #!), so the kernel runs the "
                        "interpreter its #! line names, not this file, and the program this check judged by that "
                        "name is not the one the gate runs; " + PINNED_PYTHON3_REMEDY)
        return
    if sys.platform.startswith("linux"):
        try:
            kernel = os.stat(PROC_SELF_EXE)
        except OSError as error:
            boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "cannot be compared with the program the kernel runs for "
                            "this check ({}: {})".format(PROC_SELF_EXE, error.strerror or error))
            return
        if (kernel.st_dev, kernel.st_ino) != (pinned_metadata.st_dev, pinned_metadata.st_ino):
            try:
                kernel_name = os.readlink(PROC_SELF_EXE)
            except OSError:
                kernel_name = "another file"
            boundary.refuse(pinned, PINNED_PYTHON3_PLACE, "is the name the interpreter running this check gives "
                            "itself (its argv[0]), but the kernel runs {} ({}), so the program this check judged is "
                            "not the one the gate runs; {}".format(kernel_name, PROC_SELF_EXE,
                                                                   PINNED_PYTHON3_REMEDY))
            return
    judge_venv_configurations(boundary, pinned, PINNED_PYTHON3_PLACE)


# The kernel's own name for the running program (Linux procfs). It is read
# with stat (device and inode), never judged as a path.
PROC_SELF_EXE = "/proc/self/exe"
# The file that makes a python3 a virtual environment's: site.venv and
# getpath look for it in the directory of the name python3 runs as (its
# own executable name, made absolute without resolving a symlink) and in that
# directory's parent, and a found one moves sys.prefix there and puts that
# prefix's site-packages on the import path.
VENV_CONFIGURATION = "pyvenv.cfg"
VENV_PLACE = "a pyvenv.cfg python3 reads at startup"
LEG_PYTHON3_PLACE = "the python3 a leg starts by name (the first on the run's PATH)"
LEG_PYTHON3_REMEDY = ("remedy: give the run a PATH whose first python3, after the gate_env.sh prelude has put "
                      "$HOME/.elan/bin first, is the file the gate pins and is reached by a name with no virtual "
                      "environment around it (remove that python3, or deactivate the virtual environment) "
                      "(OD-XHOST-GATE-CWD-20261025)")


def venv_configurations(executable):
    """The pyvenv.cfg files python3 looks for when it runs as `executable`
    (site.venv and getpath, CPython 3.9 to 3.14): in the directory of that
    name and in its parent, for the name as given and as os.path.abspath
    spells it (lexically, `..` removed), in that order and without repeats."""
    found = []
    for spelling in (executable, os.path.abspath(executable)):
        directory = os.path.dirname(spelling)
        for candidate in (os.path.join(directory, VENV_CONFIGURATION),
                          os.path.join(os.path.dirname(directory), VENV_CONFIGURATION)):
            if candidate not in found:
                found.append(candidate)
    return found


def judge_venv_configurations(boundary, executable, place):
    """Each pyvenv.cfg python3 would read running as `executable`, judged as
    a path (resolve): an existing one is a file nobody else may change, and a
    missing one one nobody else may create (the directory it would be created
    in is judged without the sticky exemption), since a pyvenv.cfg created
    after this check would move the import path of every later python3 run by
    that name. Returns the ones that exist."""
    existing = []
    for configuration in venv_configurations(executable):
        if boundary.resolve(configuration, place) is not None:
            existing.append(configuration)
    return existing


def find_command(name, search_path):
    """The file a PATH lookup of the bare `name` finds on `search_path`, as
    bash's `type -P`, execvp and shutil.which find it: the first entry
    holding a file of that name this user may execute that is not a
    directory. Only absolute entries are searched (judge_search_path refuses
    any other). None when there is none."""
    for entry in search_path.split(os.pathsep):
        if not entry or not os.path.isabs(entry):
            continue
        candidate = os.path.join(entry, name)
        if os.path.exists(candidate) and os.access(candidate, os.X_OK) and not os.path.isdir(candidate):
            return candidate
    return None


def judge_leg_python3(boundary, search_path, pinned):
    """The python3 a leg starts by name (repair round 4 of
    OD-XHOST-GATE-CWD-20261025): Cargo tests, Clean's tests and every
    `#!/usr/bin/env python3` script a leg runs find `python3` on the run's
    PATH, the gate_env.sh prelude's ($HOME/.elan/bin first), not by the gate's
    pin. This check judges the import path and user site-packages of the
    interpreter running it, the pinned one, so the legs' python3 must be that
    interpreter, with that import path: the first python3 on `search_path`,
    resolved hop by hop (resolve), must be the pinned file (canonical path,
    device and inode), and the pyvenv.cfg files python3 reads for the name it
    is found by must be the pinned file's, or none: when the two names lie in
    different directories, any pyvenv.cfg for either refuses (a virtual
    environment's bin/python3 is a symlink to the base interpreter, which
    the gate pins, while a leg running it gets the environment's
    site-packages). A python3 that is another file (a wrapper, a copy,
    another installation) refuses without running."""
    found = find_command("python3", search_path)
    if found is None:
        boundary.refuse("python3", LEG_PYTHON3_PLACE, "is not found on the run's PATH, although the gate pins {} "
                        "from it; {}".format(pinned, LEG_PYTHON3_REMEDY))
        return
    boundary.places.append("{} {}".format(LEG_PYTHON3_PLACE, found))
    canonical = boundary.resolve(found, LEG_PYTHON3_PLACE)
    if canonical is None:
        boundary.refuse(found, LEG_PYTHON3_PLACE, "does not resolve to an existing file; " + LEG_PYTHON3_REMEDY)
        return
    try:
        found_metadata = os.stat(canonical)
        pinned_metadata = os.stat(pinned)
    except OSError as error:
        boundary.refuse(found, LEG_PYTHON3_PLACE, "cannot be examined ({})".format(error.strerror or error))
        return
    if canonical != pinned or (found_metadata.st_dev, found_metadata.st_ino) != (
            pinned_metadata.st_dev, pinned_metadata.st_ino):
        boundary.refuse(found, LEG_PYTHON3_PLACE, "is not the gate's pinned python3 {} (it resolves to {}), so a leg "
                        "that starts python3 by name runs an interpreter whose import path and user site-packages "
                        "this check did not judge (it judges the pinned one's); {}".format(
                            pinned, canonical, LEG_PYTHON3_REMEDY))
        return
    found_configurations = judge_venv_configurations(boundary, found, VENV_PLACE)
    pinned_configurations = venv_configurations(pinned)
    if venv_configurations(found) == pinned_configurations:
        return  # the same directories: python3 reads the same pyvenv.cfg for both names
    for configuration in found_configurations + [path for path in pinned_configurations if os.path.lexists(path)]:
        boundary.refuse(configuration, LEG_PYTHON3_PLACE, "is a virtual environment's configuration python3 reads "
                        "at startup, and a leg runs the pinned interpreter as {} while the gate runs it as {}: their "
                        "import paths differ by what it names, and this check judged the gate's; {}".format(
                            found, pinned, LEG_PYTHON3_REMEDY))


def judge_darwin_c_oracle(boundary):
    """Judge Apple's selected compiler, resources and SDK before any C leg.

    Discovery is absolute so Lean's bundled clang cannot shadow the oracle.
    The identity probe independently records the same two xcrun answers.
    """
    xcrun = "/usr/bin/xcrun"
    place = "the Darwin C oracle"
    if boundary.resolve(xcrun, place) is None or boundary.refusals:
        return
    selected = []
    for arguments in (("--find", "clang"), ("--show-sdk-path",)):
        try:
            result = subprocess.run([xcrun, "--sdk", "macosx", *arguments],
                                    capture_output=True, check=False, timeout=30)
            value = result.stdout.decode("utf-8").strip()
        except (OSError, UnicodeError, subprocess.TimeoutExpired) as error:
            boundary.refuse(xcrun, place, "discovery failed: {}".format(error))
            return
        if result.returncode or not value or len(value.splitlines()) != 1 or not os.path.isabs(value):
            boundary.refuse(xcrun, place, "discovery returned no single absolute path")
            return
        selected.append(value)
    compiler, sdk = selected
    if boundary.resolve(compiler, place) is not None:
        boundary.judge_tree(_install_root(compiler, boundary, place), "the Darwin C compiler install root")
    boundary.judge_tree(sdk, "the Darwin C oracle SDK")


def judge_all(args, boundary):
    environ = os.environ
    home = environ.get("HOME", "")
    for name in GIT_OBJECT_STORE_VARIABLES:
        if name in environ:
            boundary.refuse("${}".format(name), "the environment", "is set, so git would read objects from a "
                            "store no rule here judges; an --attest run's environment allowlist removes it (LD-75)")
    relative = set()
    for name in LOCATION_VARIABLES:
        value = environ.get(name)
        if value is not None and not os.path.isabs(value):
            relative.add(name)
            boundary.refuse("${}".format(name), "the environment", "is {!r}, not an absolute path, so what it names "
                            "depends on the working directory of each program that reads it, and this check cannot "
                            "judge it; remedy: unset it or set it to an absolute path (LD-75)".format(value))

    def location(name, default=None):
        # The variable's (absolute) value, else `default`; None once refused.
        return None if name in relative else environ.get(name) or default

    for path in (GROUP_FILE, PASSWD_FILE, NSSWITCH, LOGIN_DEFS) + tuple(
            environ[name] for name in (EXTRA_GROUP_VARIABLE, EXTRA_PASSWD_VARIABLE) if environ.get(name)):
        boundary.resolve(path, "account database")
    boundary.resolve(sys.executable, "the python3 running the gate's checks")
    pinned_python3 = getattr(args, "python3", None)
    if pinned_python3 is not None:
        judge_pinned_python3(boundary, pinned_python3)
    for tool in args.tool:
        boundary.resolve(tool, "a program the gate runs")
    boundary.judge_search_path(args.search_path)
    if pinned_python3 and os.path.isabs(pinned_python3):
        # The import path judged below is the pinned interpreter's: the
        # python3 a leg finds by name on the legs' PATH must be that one
        # (repair round 4 of OD-XHOST-GATE-CWD-20261025).
        judge_leg_python3(boundary, args.search_path, pinned_python3)
    if getattr(args, "darwin_c_oracle", False):
        judge_darwin_c_oracle(boundary)
    for directory, what in ((home, "HOME"), (environ.get("XDG_CONFIG_HOME"), "XDG_CONFIG_HOME")):
        if directory:
            boundary.places.append("{} {}".format(what, directory))
            boundary.resolve(directory, what)
    for entry in sys.path:
        if entry and os.path.isabs(entry):
            boundary.places.append("python3 import path {}".format(entry))
            boundary.judge_tree(entry, "python3 import path")
    # A python3 run without -I also imports from the user's site-packages and
    # runs its .pth files (and a usercustomize) at startup: judged below
    # (the tree, and judge_user_site). Every python3 the gate scripts start,
    # inline (`-c`, `-`) or a script, runs with -I, which leaves out the user
    # site and the working directory, which no check judges; a python3 a leg
    # starts may not (OD-XHOST-GATE-CWD-20261025 and its repair round 2).
    try:
        import site
        user_site = site.getusersitepackages()
    except (ImportError, AttributeError):
        user_site = None
    # The run's temporary directory: another user may not replace what the
    # legs create there (a sticky directory such as /tmp protects it). An
    # empty TMPDIR is not /tmp to every program: Rust's std::env::temp_dir()
    # returns the empty path, so temporary files land in each program's
    # working directory, which this check does not judge (LD-75 repair).
    if environ.get("TMPDIR") == "":
        boundary.refuse("$TMPDIR", "the environment", "is empty, so Rust programs put their temporary files in "
                        "their working directory, which this check cannot judge; remedy: unset it or set it to "
                        "an absolute path (LD-75)")
    boundary.places.append("TMPDIR {}".format(environ.get("TMPDIR") or "/tmp"))
    boundary.judge_scratch_directory(environ.get("TMPDIR") or "/tmp", "TMPDIR")
    trees = [
        (location("CARGO_HOME", os.path.join(home, ".cargo")), "CARGO_HOME"),
        (location("RUSTUP_HOME", os.path.join(home, ".rustup")), "RUSTUP_HOME"),
        (location("ELAN_HOME", os.path.join(home, ".elan")), "ELAN_HOME"),
    ]
    if location("CARGO_TARGET_DIR"):
        trees.append((environ["CARGO_TARGET_DIR"], "CARGO_TARGET_DIR"))
    if user_site:
        trees.append((user_site, "python3's user site-packages"))
    # node's legacy global module folders, which require() searches.
    trees.append((os.path.join(home, ".node_modules"), "node's global modules"))
    trees.append((os.path.join(home, ".node_libraries"), "node's global modules"))
    if sys.platform == "darwin":
        # scripts/trust_cargo.sh puts $HOME/lib on DYLD_FALLBACK_LIBRARY_PATH.
        trees.append((os.path.join(home, "lib"), "HOME/lib (the macOS dynamic library fallback)"))
    if location("ATPKG_BIN"):
        trees.append((os.path.dirname(environ["ATPKG_BIN"].rstrip(os.sep)), "aterm's managed packages"))
    if sys.platform == "darwin":
        trees.append((os.path.join(home, "Library", "Application Support", "aterm", "pkg"),
                      "aterm's managed packages"))
    else:
        trees.append((os.path.join(home, ".local", "share", "aterm", "pkg"), "aterm's managed packages"))
    for name in ("trustc", "targo"):
        found = shutil.which(name, path=args.search_path)
        if found:
            what = "the Trust package of the PATH {}".format(name)
            trees.append((_install_root(found, boundary, what), what))
    for tool in args.tool_root:
        if boundary.resolve(tool, "a program the gate runs") is not None:
            what = "the install root of {}".format(tool)
            trees.append((_install_root(tool, boundary, what), what))
    for path, what in trees:
        # A root that is not absolute is refused by judge_tree (resolve).
        if path:
            boundary.places.append("{} {}".format(what, path))
            boundary.judge_tree(path, what)
    if user_site:
        judge_user_site(boundary, user_site)
    repos = [args.candidate] + list(args.git_repo)
    boundary.places.append("the candidate checkout {}".format(args.candidate))
    boundary.judge_tree(args.candidate, "the candidate checkout")
    # The WORK TREES of the Clean, AY and aterm sources, as whole trees with
    # the ANOTHER-USER rule (not require-private-tree's strict no-group-write
    # rule, which would refuse this host's 0775 user-private-group trees):
    # git runs the preflight's `git fetch origin`, its lazy-fetch cat-files,
    # `git worktree add`'s parent, the aterm commands and export_vt_tables in
    # these directories, so a program or file git's child finds by a relative
    # name in that directory or below it is judged where git resolves it
    # (finding (3); OD-XHOST-TRANSPORT-WORDS-20261024). This covers only names
    # that stay in git's working directory: a command key's later word that
    # could leave it (`..`, an option's attached path, `~user`, an
    # environment assignment) is refused in judge_git_command_value, and an
    # absolute directory it names is judged there as a tree. The candidate is
    # already judged above. That git's working directory IS this tree (no
    # core.worktree elsewhere, not a subdirectory of another repository) is
    # verified with git itself in judge_git (judge_git_layout, repair round 3).
    for repo in args.git_repo:
        boundary.places.append("the source work tree {}".format(repo))
        boundary.judge_tree(repo, "the source work tree {}".format(repo))
    for repo in repos:
        if boundary.resolve(repo, "a git repository the gate reads") is None:
            continue
        for git_dir in git_directories(repo):
            boundary.places.append("git directory {}".format(git_dir))
            boundary.judge_tree(git_dir, "the git directory of {}".format(repo))
            judge_alternates(boundary, git_dir, "the git directory of {}".format(repo))
    # Cargo's configuration search above every directory a Cargo leg runs in
    # or keeps its state in (LD-75).
    cargo_roots = [(args.candidate, "the candidate checkout")]
    try:
        cargo_roots.append((os.path.join(_private_cache().user_cache_base(environ), "trust-cg"),
                            "the user cache's trust-cg directory"))
    except ValueError:
        pass  # no user cache: the gate refuses its pinned checkouts itself
    cargo_home = location("CARGO_HOME", os.path.join(home, ".cargo"))
    if cargo_home:
        cargo_roots.append((cargo_home, "CARGO_HOME"))
    if location("CARGO_TARGET_DIR"):
        cargo_roots.append((environ["CARGO_TARGET_DIR"], "CARGO_TARGET_DIR"))
    cargo_roots += [(root, "a directory the gate runs Cargo in") for root in args.cargo_root]
    for root, what in cargo_roots:
        boundary.places.append("Cargo's configuration search above {} {}".format(what, root))
        boundary.judge_cargo_ancestry(root, "Cargo's configuration search above " + what)
    # git's fetch may run ssh in any --attest run (the pinned checkouts' `git
    # fetch origin`, Cargo's git sources), not only with an x86-64 executor:
    # ssh's configuration and every transport program the environment names
    # are judged in every run (OD-XHOST-FETCH-TRANSPORT-20261016); those git's
    # configuration names are judged in judge_git.
    # OpenSSH reads ~/.ssh of the PASSWD home, not of $HOME (strace: with HOME
    # elsewhere ssh still opens the passwd home's .ssh/config), so both are
    # judged; on this host they are the same directory (finding (5)).
    ssh_homes = [home]
    try:
        passwd_home = pwd.getpwuid(boundary.euid).pw_dir
    except KeyError:
        passwd_home = ""
    if passwd_home and passwd_home not in ssh_homes:
        ssh_homes.append(passwd_home)
    ssh_configs = [os.path.join(base, ".ssh") for base in ssh_homes if base] + ["/etc/ssh"]
    for path in ssh_configs:
        boundary.places.append("ssh configuration {}".format(path))
        boundary.judge_tree(path, "ssh configuration")
    # The shell ssh runs a ProxyCommand/LocalCommand through, and git runs
    # every shell-command configuration key through: $SHELL (ssh execv()s it
    # with no PATH search, so a relative value would resolve in ssh's working
    # directory; refuse it) and /bin/sh (git's SHELL_PATH and ssh's fallback),
    # both judged as tools (finding (4)).
    shell_value = environ.get("SHELL")
    if shell_value:
        boundary.places.append("$SHELL {}".format(shell_value))
        if not os.path.isabs(shell_value):
            boundary.refuse("$SHELL", "the environment", "is {!r}, not an absolute path, but ssh runs a "
                            "ProxyCommand through it with no PATH search, so it would resolve in ssh's working "
                            "directory, which this check cannot judge; remedy: unset it or set it to an absolute "
                            "path (OD-XHOST-TRANSPORT-WORDS-20261024)".format(shell_value))
        else:
            boundary.resolve(shell_value, "$SHELL (the shell ssh and git run commands through)")
    boundary.places.append("the system shell /bin/sh")
    boundary.resolve("/bin/sh", "the system shell /bin/sh")
    for name, shell in TRANSPORT_VARIABLES:
        if name in environ:
            boundary.places.append("${} (a program git's fetch runs)".format(name))
            judge_transport_program(boundary, environ[name], "${}".format(name),
                                    "{} in the environment".format(name), args.search_path, shell)
    if "ext" in environ.get("GIT_ALLOW_PROTOCOL", "").split(":"):
        boundary.refuse("$GIT_ALLOW_PROTOCOL", "the environment", "lists ext, so git's ext:: transport may run the "
                        "command a remote URL names, which this check does not judge; an --attest run's "
                        "environment allowlist removes and refuses it (OD-XHOST-FETCH-TRANSPORT-20261016)")
    # Cargo's git databases ($CARGO_HOME/git/db/<name>-<hash>, bare): with
    # net.git-fetch-with-cli Cargo runs `git fetch` in each, so each one's own
    # configuration and git's view of it are judged as a --git-repo's are
    # (judge_git; repair round 3). The tree itself was judged with CARGO_HOME.
    cargo_git_databases = []
    if cargo_home and os.path.isabs(cargo_home):
        database_root = os.path.join(cargo_home, "git", "db")
        try:
            names = sorted(os.listdir(database_root))
        except OSError:
            names = []
        cargo_git_databases = [os.path.join(database_root, name) for name in names
                               if os.path.isdir(os.path.join(database_root, name))]
    # Cargo's git checkouts ($CARGO_HOME/git/checkouts/<name>/<rev>), where
    # Cargo can run git for a submodule: git's view of each one and its own
    # configuration are judged, and each repository nested in it (Cargo makes
    # its checkout submodules embedded repositories) is judged as one
    # (OD-XHOST-GIT-PROGRAM-KEYS-20261024, repair round 2).
    cargo_checkouts = []
    if cargo_home and os.path.isabs(cargo_home):
        checkout_root = os.path.join(cargo_home, "git", "checkouts")
        try:
            groups = sorted(os.listdir(checkout_root))
        except OSError:
            groups = []
        for group in groups:
            try:
                revisions = sorted(os.listdir(os.path.join(checkout_root, group)))
            except OSError:
                continue
            cargo_checkouts += [os.path.join(checkout_root, group, revision) for revision in revisions
                                if os.path.lexists(os.path.join(checkout_root, group, revision, ".git"))]
    judge_git(boundary, args.search_path, repos + cargo_git_databases, cargo_checkouts)


def _config_quote(text):
    """`text` as a double-quoted git configuration value or subsection; None
    when it holds a character this writer does not spell (a control
    character other than tab and newline)."""
    if any(ord(character) < 0x20 and character not in "\t\n" for character in text):
        return None
    return '"{}"'.format(text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t"))


def gate_git_config_text(carried):
    """The text of the gate's git configuration file and the (key, value)
    pairs `git config --file <it> --list` must read back, or (None, why)."""
    lines = ["# The git configuration of one attested soundness run, written by scripts/host_boundary.py",
             "# (OD-XHOST-GIT-PROGRAM-KEYS-20261024). The run's git reads it as its global configuration",
             "# (GIT_CONFIG_GLOBAL) and no system configuration (GIT_CONFIG_NOSYSTEM=1)."]
    expected = []
    entries = [("{}.{}".format(section, name) if subsection is None else "{}.{}.{}".format(section, subsection, name),
                value.encode()) for section, subsection, name, value in GATE_GIT_SETTINGS] + list(carried or [])
    for raw_key, raw_value in entries:
        section, subsection, name = split_config_key(raw_key)
        # A key with no `=` (raw_value None: `[credential] useHttpPath`, which
        # git reads as true) is written the same way, with no value.
        try:
            value = None if raw_value is None else raw_value.decode("utf-8")
            if subsection is not None:
                subsection.encode("utf-8")
        except UnicodeError:
            return None, "the carried key {!r} has a value that is not UTF-8 text".format(raw_key)
        quoted_value = "" if value is None else _config_quote(value)
        header = "[{}]".format(section) if subsection is None else None
        if subsection is not None:
            quoted_subsection = _config_quote(subsection)
            if quoted_subsection is None or "\n" in subsection:
                return None, "the carried key {!r} has a subsection this writer cannot spell".format(raw_key)
            header = "[{} {}]".format(section, quoted_subsection)
        if quoted_value is None or not re.fullmatch(r"[A-Za-z0-9-]+", section) or not re.fullmatch(
                r"[A-Za-z][A-Za-z0-9-]*", name):
            return None, "the carried key {!r} cannot be written exactly".format(raw_key)
        lines += [header, "\t{}".format(name) if value is None else "\t{} = {}".format(name, quoted_value)]
        expected.append(("{}.{}".format(section.lower(), name.lower()) if subsection is None else
                         "{}.{}.{}".format(section.lower(), subsection, name.lower()), value))
    return "\n".join(lines) + "\n", expected


def write_gate_git_config(boundary, search_path):
    """Write the gate's git configuration (the carried keys judge_git
    collected, and GATE_GIT_SETTINGS) to a new 0600 file in a new 0700
    directory below TMPDIR (else /tmp; judged as the run's scratch
    directory), read it back with git, and return its path; on any failure
    refuse and return None. The run then exports GIT_CONFIG_GLOBAL=<path>
    and GIT_CONFIG_NOSYSTEM=1, so no git it starts reads a system or global
    key this check did not judge (OD-XHOST-GIT-PROGRAM-KEYS-20261024)."""
    import tempfile
    place = "the gate's git configuration"
    git = shutil.which("git", path=search_path)
    text, expected = gate_git_config_text(boundary.carried)
    if text is None or git is None:
        boundary.refuse("(gate git configuration)", place, expected if text is None else "no git on PATH")
        return None
    try:
        directory = tempfile.mkdtemp(prefix="soundness-git.", dir=os.environ.get("TMPDIR") or "/tmp")
        path = os.path.join(directory, "config")
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0), 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            os.fchmod(handle.fileno(), 0o600)
            handle.write(text)
    except OSError as error:
        boundary.refuse("(gate git configuration)", place, "cannot be written ({})".format(error.strerror or error))
        return None
    rc, out = _git(git, ["config", "--file", path, "--list", "-z"])
    read = []
    for field in out.split(b"\0")[:-1] if rc == 0 else []:
        key, separator, value = field.decode("utf-8", "replace").partition("\n")
        read.append((key, value if separator else None))
    if rc != 0 or read != expected:
        boundary.refuse(path, place, "does not read back as the keys written (git read {!r}, expected {!r})".format(
            read, expected))
        return None
    return path


def _private_cache():
    """scripts/private_cache.py, the one cache-base rule (imported from this
    file's directory: `python3 -I` puts no script directory on sys.path)."""
    directory = os.path.dirname(os.path.abspath(__file__))
    if directory not in sys.path:
        sys.path.insert(0, directory)
    import private_cache  # noqa: E402
    return private_cache


def _canonical(boundary, path, place):
    """`path` canonical as `boundary.resolve` follows it hop by hop (so a hop
    into /proc or /dev/fd refuses there, which os.path.realpath would instead
    follow in this checker's own view), else its lexical normal form, which
    the caller's judge_tree then resolves and judges (a missing path)."""
    canonical = boundary.resolve(path, place)
    return canonical if canonical is not None else os.path.normpath(path)


def _install_root(path, boundary, place):
    """The install root of the program `path`: the directory above the `bin`
    directory its canonical file (an atpkg launcher shim followed) is in.
    Both the program and the shim's exec target are followed by
    `Boundary.resolve`, not os.path.realpath: a shim that execs
    `/proc/self/cwd/...` names the checker's own working directory to
    realpath, so its install root would be judged in the wrong place (a low
    of the X-HOST-P13 round-5 repair's verifier; OD-XHOST-TRANSPORT-WORDS-20261024)."""
    canonical = _canonical(boundary, path, place)
    try:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from trust_toolchain import launcher_target  # noqa: E402
        from pathlib import Path
        target = launcher_target(Path(canonical))
        if target is not None:
            canonical = _canonical(boundary, str(target), place)
    except ImportError:
        pass
    return os.path.dirname(os.path.dirname(canonical))


def main(argv=None):
    parser = argparse.ArgumentParser(description="the host trust boundary of an attested run (LD-73)")
    parser.add_argument("--search-path", required=True, help="the PATH the run's legs use")
    parser.add_argument("--candidate", help="the candidate checkout")
    parser.add_argument("--python3", help="the gate's pinned python3 (SOUNDNESS_PYTHON3): judged as exactly that "
                                          "file, which must be the interpreter running this check")
    parser.add_argument("--gate-git-config", action="store_true",
                        help="on a pass, write the run's own git configuration and print its path")
    parser.add_argument("--judge-git-config", metavar="DIR",
                        help="judge only the repository-local configuration git reads in DIR (a pinned checkout) "
                             "and in every repository nested in its work tree")
    parser.add_argument("--git-repo", action="append", default=[], help="another repository git runs in")
    parser.add_argument("--tool", action="append", default=[], help="a program the gate runs by path")
    parser.add_argument("--tool-root", action="append", default=[],
                        help="a program the gate runs by path, judged with its whole install root")
    parser.add_argument("--darwin-c-oracle", action="store_true",
                        help="judge the Apple compiler and SDK selected by absolute xcrun discovery")
    parser.add_argument("--cargo-root", action="append", default=[],
                        help="a directory the gate runs Cargo in or below (its ancestors' .cargo is judged)")
    args = parser.parse_args(argv)
    if (args.candidate is None) == (args.judge_git_config is None):
        parser.error("give exactly one of --candidate and --judge-git-config")
    accounts = Accounts(os.geteuid(), os.environ.get(EXTRA_GROUP_VARIABLE), os.environ.get(EXTRA_PASSWD_VARIABLE))
    boundary = Boundary(accounts)
    gate_config = None
    try:
        if args.judge_git_config is not None:
            git = shutil.which("git", path=args.search_path)
            if git is None:
                boundary.refuse(args.judge_git_config, "git configuration", "no git on the run's PATH")
            elif judge_repository_configuration(boundary, git, args.judge_git_config, args.search_path,
                                                local_only=True) is not None and not boundary.refusals:
                print("host_boundary: PASS: the repository-local configuration of {} and of every repository "
                      "nested in its work tree names no key off the allowlist "
                      "(OD-XHOST-GIT-PROGRAM-KEYS-20261024)".format(args.judge_git_config))
                return 0
        else:
            judge_all(args, boundary)
            if args.gate_git_config and not boundary.refusals:
                gate_config = write_gate_git_config(boundary, args.search_path)
    except _TooMany:
        pass
    except OSError as error:
        # Something judged could not be examined: nothing is accepted.
        boundary.refusals.append("{} (the check itself): could not be examined ({})".format(
            getattr(error, "filename", None) or "?", error.strerror or error))
    if args.judge_git_config is not None:
        for refusal in boundary.refusals:
            print("host_boundary: REFUSED " + refusal)
        print("host_boundary: FAIL: the repository-local configuration of {} cannot be judged or names a key off "
              "the allowlist; {}".format(args.judge_git_config, LOCAL_KEY_REMEDY))
        return 1
    for place in boundary.places:
        print("host_boundary: judged " + place)
    for entry in sorted(boundary.system_owned):
        print("host_boundary: accepted a system account's file in a root-owned directory: " + entry)
    if boundary.refusals:
        for refusal in boundary.refusals:
            print("host_boundary: REFUSED " + refusal)
        more = " (and possibly more: the check stops at {})".format(REFUSAL_LIMIT) \
            if len(boundary.refusals) >= REFUSAL_LIMIT else ""
        writable = boundary.writable_refusals
        other = len(boundary.refusals) - writable
        if not other:
            print("host_boundary: FAIL: {} path(s) this run would execute or read can be written by another user{}; "
                  "{}".format(len(boundary.refusals), more, REMEDY))
            return 1
        # Not every refusal is a path another user can write (an off-allowlist
        # git key, git's view of a repository, a relative location, ...): the
        # writability remedy is named only for those that are.
        parts = ["{} refusal(s) of a setting, location, repository or git configuration key this check cannot "
                 "judge or refuses outright, each REFUSED line above giving the reason and its remedy".format(other)]
        if writable:
            parts.append("{} path(s) this run would execute or read can be written by another user; {}".format(
                writable, REMEDY))
        print("host_boundary: FAIL: {} refusal(s){}: {}".format(len(boundary.refusals), more, "; and ".join(parts)))
        return 1
    if gate_config is not None:
        for section, _subsection, name, value in GATE_GIT_SETTINGS:
            print("host_boundary: gate git configuration sets {}.{}={}".format(section, name, value))
        for raw_key, _raw_value in boundary.carried or []:
            # Values are not printed: a credential username is the user's.
            print("host_boundary: gate git configuration carries {}".format(raw_key))
        print(GATE_GIT_CONFIG_LINE + gate_config)
    # What this check established, and no more: what it does not judge is its
    # module docstring's NOT JUDGED list (OD-XHOST-GATE-CWD-20261025; the line
    # had said no tool or configuration the run executes or reads is writable
    # by another user, while the run imported modules from its caller's
    # working directory, which no check judges).
    print("host_boundary: PASS: {} entries in {} judged places ({} trees); no judged place, and nothing in one, "
          "is writable by another user (not judged: the NOT JUDGED list of scripts/host_boundary.py; LD-73, "
          "OD-XHOST-GATE-CWD-20261025; account databases: {})".format(
              boundary.entries, len(boundary.places), len(boundary.trees), ", ".join(accounts.sources) or "none"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
