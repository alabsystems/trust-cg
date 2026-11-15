#!/usr/bin/env python3
"""Owner-private directories and files under the trust-cg user cache, for scripts.

    python3 -I scripts/private_cache.py mkdir DIR [DIR ...]
    python3 -I scripts/private_cache.py cache-base
    python3 -I scripts/private_cache.py require-private PATH [PATH ...]
    python3 -I scripts/private_cache.py require-private-tree DIR [DIR ...]
    python3 -I scripts/private_cache.py export-commit REPO COMMIT DESTINATION PATH [PATH ...]

`export-commit` writes the directories PATH of COMMIT into the new private
directory DESTINATION from the object store by hash (`export_commit_paths`;
the soundness gate's export of the attested commit's own proofs) and prints
its canonical path.

`require-private` prints the canonical path of each PATH it accepts, one per
line; callers execute or write through exactly that path (see the last item
of the rule below). `require-private-tree` does the same for a directory
whose WHOLE tree it judged (the soundness gate's pinned checkouts, which it
builds and runs Clean from).

trust-cg itself creates everything under `<cache>/trust-cg` through
`trust_cg_process_env::private_fs` (crates/trust-cg-process-env/src/private_fs.rs).
`<cache>` is resolved by ONE rule, `user_cache_base` here and
`private_fs::user_cache_base` in trust-cg: `$XDG_CACHE_HOME` when it is an
absolute path (an empty or relative value is ignored, as the XDG Base
Directory specification requires), else `$HOME/.cache` when HOME is absolute,
else no cache. This module is the same rule for the repository's scripts,
written once: scripts/soundness_check.sh runs its `cache-base`, `mkdir` and
`require-private` commands, scripts/check_x86_icmp_certificates.py imports it,
and scripts/soundness_remote.sh sends its source to the x86-64 executor, which
has no checkout of its own when it creates its cache directories.

Why: AY is started only from a private copy under `<cache>/trust-cg/ay-exec`,
and the identity rule refuses that copy when an ancestor directory is writable
by group or others without the sticky bit
(crates/trust-cg-verify/src/ay_private_copy.rs). `mkdir -p` and
`Path.mkdir(parents=True)` create with mode `0777 & ~umask`, which is `0775`
under umask `0002` (Ubuntu's default for a user with a user-private group). A
script that created `<cache>/trust-cg` that way refused AY in every later
process on the host (X-HOST-P13 closure audit, 2026-10-03: soundness-deps,
ay-cli, and the x86-64 executor's cache).

The rule:

* every directory this module CREATES has mode exactly 0700, whatever the
  umask. It is made with mode 0700 under umask 077, so no owner bit can be
  missing; when a set-group-ID parent passed its bit on, the mode is set to
  0700 through a descriptor opened on the new directory without following a
  symlink. A new directory that cannot be made 0700 is removed again and the
  call fails;
* a default POSIX ACL the new directory inherited from its parent is removed
  from it (Linux), through the same descriptor. A default ACL overrides the
  umask for whatever is later created inside, so with one inherited, git, tar
  and cargo running under umask 077 below the new directory still wrote
  group-writable entries. A directory that already existed keeps its own
  ACL; where the platform has no extended-attribute call (macOS) nothing is
  removed;
* a directory that already exists (a symlink to one included) is never
  changed, whatever its mode. Judging it is the caller's business
  (`canonical_owner_private_directory`);
* files are created exclusively (`O_EXCL`, never through a symlink) with mode
  exactly 0600 (`create_private_file`);
* a subprocess that writes inside such a directory (git, tar, cargo) runs
  under `PRIVATE_UMASK` (`private_umask()`), so what it creates there is
  private too;
* what a script executes from below the cache (the icmp gate's AY, the
  soundness gate's Clean checker) is executed only after `require_private`
  accepted it: every canonical ancestor is owned by this user or root and no
  other user may rename entries in it (the rule AY's private copy is held
  to), and the executable itself is a regular file no other user can write.
  A directory that fails is refused by name with the remedy, never repaired;
* the path that is checked is the CANONICAL path, so the caller resolves the
  name once, through `require_private` (`require-private` prints it), and
  from then on uses exactly that canonical path, never the name it started
  from. No other user can change an entry along the canonical path once it
  passed, but the original name may run through a symlink in a directory
  others can write, which they can re-point after the check (X-HOST-P13
  third closure audit: a cache reached as `<shared 0777>/link` passed the
  check and the soundness gate then ran another program as Clean through
  the link). `trust_cg_process_env::private_fs::canonical_owner_private_directory`
  states the same contract;
* a directory tree a script builds and runs a checker from (the soundness
  gate's pinned Clean checkout: its sources, its `target/` and the binary
  the build leaves there) is accepted only by `require_private_tree`: the
  directory as `require_private` judges it, and then EVERY entry below it,
  each directory judged before it is listed: owned by this user, no
  group/other write bit, a directory or a regular file, or a symlink whose
  resolution, hop by hop through its literal target, never leaves the tree
  (X-HOST-P13 fifth closure audit: judging only where a link resolved at
  check time accepted one that ran out through a directory others can write
  and back in). No directory or file of the tree, its root included, may
  carry a POSIX access ACL, and no directory a default ACL, that lets
  anyone but this user write (a named user other than this user and root,
  any group whoever its members are, or every user), read by
  scripts/host_boundary.py's ACL reader: a default ACL decides who can
  write what is created in the directory later, whatever the umask (the
  X-HOST-P13 round-4 verifier: a pinned checkout with one passed until the
  check after its build, by when Cargo had run build scripts from it). A
  judged entry can afterwards be changed only by this user or root, so the
  whole tree is fixed for the rest of the run.
  Judging the root alone let another user rewrite a proof file the checker
  read in a `0775` subdirectory mid-run and turn a failing pinned proof into
  an attested pass (X-HOST-P13 fourth closure audit). A tree that fails is
  refused by name with `TREE_REMEDY`: delete it, since a `chmod` cannot undo
  what another user may already have written there;
* an export of a commit's files (`export_commit_paths`) is written from the
  object store by hash, never through `git archive` or a checkout: the
  commit and every tree and blob are read by `git cat-file --batch` with no
  system or global git configuration and no attributes, and each must hash
  to its name; the written files are read back and must hash to their blobs.
  `git archive` applied the smudge filters and attributes of the user's
  global git configuration (X-HOST-P13 sixth closure audit).

The process umask is set to 077 only around a creation (`private_umask()`);
another thread that creates a file meanwhile gets a more private mode, never
a less private one.

Kept compatible with Python 3.6: the x86-64 executor runs this source with
whatever python3 it has.
"""

import contextlib
import errno
import os
import stat
import sys

PRIVATE_DIRECTORY_MODE = 0o700
PRIVATE_FILE_MODE = 0o600
PRIVATE_UMASK = 0o077
# The extended attribute that holds a directory's default POSIX ACL (Linux).
DEFAULT_ACL_ATTRIBUTE = "system.posix_acl_default"
# What `removexattr` answers when there is no default ACL to remove, or the
# file system keeps none.
NO_DEFAULT_ACL_ERRNOS = {getattr(errno, name) for name in ("ENODATA", "ENOATTR", "ENOTSUP", "EOPNOTSUPP", "ENOSYS")
                         if hasattr(errno, name)}


class NotPrivateError(OSError):
    """A directory this module created could not be made 0700 (and was
    removed). Carries no errno, so no caller mistakes it for a `mkdir`
    error."""


@contextlib.contextmanager
def private_umask():
    """Run the body (and every subprocess it starts) under umask 077."""
    previous = os.umask(PRIVATE_UMASK)
    try:
        yield
    finally:
        os.umask(previous)


def _mode(metadata):
    return stat.S_IMODE(metadata.st_mode)


def _drop_default_acl(descriptor):
    """Remove the default ACL of the directory open at `descriptor`, if it
    has one (`DEFAULT_ACL_ATTRIBUTE`). No default ACL, no ACL support and no
    extended-attribute call are all nothing to do."""
    removexattr = getattr(os, "removexattr", None)
    if removexattr is None:
        return
    try:
        removexattr(descriptor, DEFAULT_ACL_ATTRIBUTE)
    except OSError as error:
        if error.errno not in NO_DEFAULT_ACL_ERRNOS:
            raise


def _create_private_dir(path):
    """Create the one directory `path` (its parent must exist), mode exactly
    0700. An existing `path` raises the `mkdir` error (`FileExistsError`). A
    directory this call created but cannot make private is removed again."""
    with private_umask():
        os.mkdir(path, PRIVATE_DIRECTORY_MODE)
    try:
        flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(path, flags)
        try:
            metadata = os.fstat(descriptor)
            if not stat.S_ISDIR(metadata.st_mode):
                raise OSError(errno.ENOTDIR, "the new entry is not a directory")
            if _mode(metadata) != PRIVATE_DIRECTORY_MODE:
                os.fchmod(descriptor, PRIVATE_DIRECTORY_MODE)
                if _mode(os.fstat(descriptor)) != PRIVATE_DIRECTORY_MODE:
                    raise OSError(errno.EPERM, "its mode is still not private after the change")
            _drop_default_acl(descriptor)
        finally:
            os.close(descriptor)
    except OSError as error:
        with contextlib.suppress(OSError):
            os.rmdir(path)
        raise NotPrivateError("created {} and cannot make it {:04o}: {}".format(
            path, PRIVATE_DIRECTORY_MODE, error.strerror or error)) from error


def create_private_dir_all(path):
    """Create `path` and every missing ancestor, each new one mode exactly
    0700 whatever the umask; every directory that already exists is left as
    it is. Returns whether THIS call created `path` itself."""
    path = os.fspath(path)
    if not path:
        return False
    try:
        _create_private_dir(path)
        return True
    except FileNotFoundError:
        pass
    except FileExistsError:
        if os.path.isdir(path):
            return False
        raise
    parent = os.path.dirname(path.rstrip(os.sep)) or os.curdir
    if parent == path:
        raise OSError(errno.ENOENT, "failed to create whole tree", path)
    create_private_dir_all(parent)
    try:
        _create_private_dir(path)
        return True
    except FileExistsError:
        if os.path.isdir(path):
            return False
        raise


def create_private_file(path):
    """Create the file `path`, which must not exist yet (an existing file or
    symlink there raises `FileExistsError`), mode exactly 0600 whatever the
    umask, and return its descriptor open for writing."""
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    descriptor = os.open(os.fspath(path), flags, PRIVATE_FILE_MODE)
    try:
        if _mode(os.fstat(descriptor)) != PRIVATE_FILE_MODE:
            os.fchmod(descriptor, PRIVATE_FILE_MODE)
    except OSError:
        os.close(descriptor)
        raise
    return descriptor


def write_private_file(path, data):
    """Write `data` (bytes or str) to a new private file `path` (see
    `create_private_file`)."""
    if isinstance(data, str):
        data = data.encode()
    with os.fdopen(create_private_file(path), "wb") as handle:
        handle.write(data)


def open_lock_file(path):
    """A lock file's descriptor, open for reading and writing: created 0600
    when missing; an existing one is opened as it is (never through a
    symlink, never truncated, its mode never changed)."""
    try:
        descriptor = create_private_file(path)
        os.close(descriptor)
    except FileExistsError:
        pass
    flags = os.O_RDWR | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    return os.open(os.fspath(path), flags)


def check_owner_only_writable(path, directory):
    """Refuse (`PermissionError`) unless `path` is a directory (when
    `directory`) or a regular file, never a symlink, owned by this effective
    user, with no group/other write bit: no other user can change it (nor,
    for a directory, replace an entry in it). Read and execute bits are
    allowed. This is what binds bytes to a record beside them (the icmp
    gate's AY slot); `check_owner_private` is the stricter rule for files
    this user's caches create."""
    path = os.fspath(path)
    metadata = os.lstat(path)
    kind_ok = stat.S_ISDIR(metadata.st_mode) if directory else stat.S_ISREG(metadata.st_mode)
    if not kind_ok:
        raise PermissionError(errno.EACCES, "{} is not a {} (symlinks are refused)".format(
            path, "directory" if directory else "regular file"))
    euid = os.geteuid()
    if metadata.st_uid != euid:
        raise PermissionError(errno.EACCES, "{} is owned by uid {}, not the effective uid {}".format(
            path, metadata.st_uid, euid))
    if metadata.st_mode & 0o022:
        raise PermissionError(errno.EACCES, "{} has mode {:04o}; another user could replace its contents".format(
            path, _mode(metadata)))
    return metadata


def check_owner_private(path, directory):
    """Refuse (`PermissionError`) unless `path` passes
    `check_owner_only_writable` and, for a file, has no group/other bit at
    all: `trust_cg_process_env::private_fs::check_owner_private`."""
    metadata = check_owner_only_writable(path, directory)
    if not directory and metadata.st_mode & 0o077:
        raise PermissionError(errno.EACCES, "{} has mode {:04o}; another user could read it".format(
            os.fspath(path), _mode(metadata)))


def canonical_owner_private_directory(path):
    """The canonical form of the directory `path`, refusing (`PermissionError`)
    unless every canonical ancestor is a directory owned by this user or root
    that no other user may rename entries in (group/other write only with the
    sticky bit, as `/tmp` has) and `path` itself passes
    `check_owner_private`: the ancestor rule AY's private copy is held to
    (`trust_cg_process_env::private_fs::canonical_owner_private_directory`).
    Nothing is changed. Every check is made on the canonical path, which is
    returned: the caller uses it instead of `path`, whose own components the
    rule does not judge (a symlink in a directory others can write may lead
    to it)."""
    canonical = os.path.realpath(os.fspath(path))
    _check_canonical_ancestors(canonical)
    check_owner_private(canonical, True)
    return canonical


def _check_canonical_ancestors(canonical):
    """Refuse (`PermissionError`) unless every ancestor of the canonical path
    `canonical`, outermost first, is a directory owned by this user or root
    that no other user may rename entries in (group/other write only with
    the sticky bit)."""
    euid = os.geteuid()
    ancestors = []
    current = os.path.dirname(canonical)
    while True:
        ancestors.append(current)
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    for ancestor in reversed(ancestors):
        metadata = os.lstat(ancestor)
        if not stat.S_ISDIR(metadata.st_mode) or metadata.st_uid not in (euid, 0) \
                or (metadata.st_mode & 0o022 and not metadata.st_mode & stat.S_ISVTX):
            raise PermissionError(errno.EACCES, "{} is not a trusted directory ancestor (uid {}, mode {:04o})".format(
                ancestor, metadata.st_uid, _mode(metadata)))


def user_cache_base(environ=None):
    """The user cache base: `$XDG_CACHE_HOME` when it is an absolute path,
    else `$HOME/.cache` when HOME is absolute. An empty or relative
    XDG_CACHE_HOME is ignored, as the XDG Base Directory specification
    requires, so no cache location ever depends on the working directory.
    Raises `ValueError` naming the variables when neither names an absolute
    directory. The same rule, with the same refusal text, as trust-cg's
    `trust_cg_process_env::private_fs::user_cache_base`, which every trust-cg
    cache root (AY's private copy among them) is resolved by."""
    environ = os.environ if environ is None else environ
    xdg = environ.get("XDG_CACHE_HOME")
    if xdg and os.path.isabs(xdg):
        return xdg
    home = environ.get("HOME")
    if home and os.path.isabs(home):
        return os.path.join(home, ".cache")
    if home is not None:
        raise ValueError("HOME={} is not absolute and XDG_CACHE_HOME names no absolute directory".format(home))
    raise ValueError("neither XDG_CACHE_HOME nor HOME names an absolute directory")


# What a refusal by `require_private` tells its owner to do.
PRIVATE_REMEDY = ("run `chmod go-w` on the directory or file named (an existing entry is never changed), "
                  "or use a cache directory (XDG_CACHE_HOME) only you can write")


def require_private(path):
    """Refuse (`PermissionError`) anything executed from, or checked out
    into, the user cache unless no other user can change it: for a directory,
    `canonical_owner_private_directory` (every canonical ancestor owned by
    this user or root and renamable by nobody else, the directory itself not
    group/other-writable); for a file, a regular file (never a symlink) that
    passes `check_owner_only_writable`, in a directory that passes the
    directory rule. Read and execute bits are allowed. Nothing is changed.

    Returns the canonical path, which is what was checked: a file's
    directory is resolved first and the file is then checked by its name in
    that canonical directory, so the returned path names the very entry the
    checks examined. The caller must use that path from here on, never `path`
    (see the module's rule)."""
    path = os.fspath(path)
    metadata = os.lstat(path)
    if stat.S_ISDIR(metadata.st_mode) or (stat.S_ISLNK(metadata.st_mode) and os.path.isdir(path)):
        return canonical_owner_private_directory(path)
    directory = canonical_owner_private_directory(os.path.dirname(path) or os.curdir)
    canonical = os.path.join(directory, os.path.basename(path))
    check_owner_only_writable(canonical, False)
    return canonical


# What a refusal by `require_private_tree` of an entry of the tree itself (its
# root included) tells its owner to do. A refusal of a directory above the
# tree takes `PRIVATE_REMEDY`.
TREE_REMEDY = ("remove the whole tree so it is created again private (for a pinned checkout, "
               "`git -C <source repository> worktree remove --force <checkout>`); an existing entry is never "
               "changed, and a chmod cannot undo what another user may already have written into it")


class UntrustedTreeError(PermissionError):
    """`require_private_tree` refused an entry of the tree itself (its root
    included), not a directory above it."""


# The most symlinks one resolution may follow (Linux's own limit, ELOOP).
SYMLINK_HOP_LIMIT = 40


def _symlink_stays_in_tree(root, entry):
    """Whether resolving the symlink `entry` (inside the canonical tree
    `root`) never leaves the tree: its literal target, and the literal
    target of every symlink met while following it, is walked component by
    component the way the kernel resolves it, and every position along the
    way is a path inside `root`. A `..` at `root` itself, an absolute target
    that does not spell `root` or a path below it, and more than
    `SYMLINK_HOP_LIMIT` symlinks all answer no.

    Judging only where the link resolved at check time (its realpath) let a
    link whose literal path ran through a directory outside the tree that
    others can write, and from there back inside, pass; re-pointing that
    outside hop afterwards made the same in-tree name resolve outside
    (X-HOST-P13 fifth closure audit). Every position this walk visits is
    inside the tree, so `require_private_tree` judges each of them: no other
    user can change where the name leads once the walk passed. A component
    that does not exist, or a name below a file, is taken lexically; the
    kernel refuses such a path, so it reaches nothing outside either."""
    prefix = root.rstrip(os.sep) + os.sep
    relative = os.path.relpath(os.path.dirname(entry), root)
    position = [] if relative == os.curdir else relative.split(os.sep)
    pending = []
    hops = 0
    link = entry
    while True:
        if link is not None:
            hops += 1
            if hops > SYMLINK_HOP_LIMIT:
                return False
            target = os.readlink(link)
            if os.path.isabs(target):
                if target != root and not target.startswith(prefix):
                    return False
                position = []
                target = target[len(root):]
            pending = [part for part in target.split(os.sep) if part] + pending
            link = None
        if not pending:
            return True
        name = pending.pop(0)
        if name == os.curdir:
            continue
        if name == os.pardir:
            if not position:
                return False
            position.pop()
            continue
        candidate = os.path.join(root, *position, name)
        try:
            metadata = os.lstat(candidate)
        except OSError as error:
            if error.errno not in (errno.ENOENT, errno.ENOTDIR):
                raise
            position.append(name)
            continue
        if stat.S_ISLNK(metadata.st_mode):
            link = candidate
            continue
        position.append(name)


class _NoGroupMayWrite(object):
    """The strict rule's view of groups for `_acl_writers`: every group
    counts as having another member, as the mode-bit rule refuses any group
    write bit whoever the group's members are."""

    @staticmethod
    def others(gid):
        return ["no group may write here (the strict rule of trust-cg's caches)"]

    @staticmethod
    def group_label(gid):
        return "gid {}".format(gid)


_HOST_BOUNDARY = []


def _host_boundary():
    """scripts/host_boundary.py, loaded from this file's directory on first
    use: its POSIX ACL reader and reading are the ones `_acl_writers`
    applies, so the two rules read ACLs one way. Refuses
    (`PermissionError`) when it cannot be loaded (this source run as
    `python3 -c`, as the x86-64 executor runs it for `mkdir`, has no file
    beside it); a tree is then never accepted."""
    if not _HOST_BOUNDARY:
        source = globals().get("__file__")
        location = os.path.join(os.path.dirname(os.path.abspath(source)), "host_boundary.py") if source else None
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location("host_boundary", location)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
        except (ImportError, OSError, AttributeError, TypeError) as error:
            raise PermissionError(errno.EACCES, "cannot judge POSIX ACLs: scripts/host_boundary.py cannot be loaded "
                                  "beside {} ({})".format(source or "this source", error))
        _HOST_BOUNDARY.append(module)
    return _HOST_BOUNDARY[0]


def _acl_writers(path, metadata):
    """Who besides this user a POSIX access ACL of `path` (whose lstat is
    `metadata`), or the default ACL of a directory, lets write it or what is
    created in it: a named user other than this user and root, any group
    (the strict rule: whoever its members are), or every user; and an ACL
    that cannot be read. Empty when none does, and where the platform has no
    extended-attribute call (macOS). A default ACL overrides the umask, so
    with one on a pinned checkout what its build creates there under umask
    077 was open to that user (X-HOST-P13 round-4 verifier)."""
    boundary = _host_boundary()
    euid = os.geteuid()
    writers = list(boundary.access_acl_writers(path, metadata, euid, _NoGroupMayWrite) or ())
    if stat.S_ISDIR(metadata.st_mode):
        writers += boundary.default_acl_writers(path, metadata, euid, _NoGroupMayWrite) or ()
    return writers


def _refuse_acl_writers(path, metadata):
    """`UntrustedTreeError` naming `path` when `_acl_writers` finds anyone."""
    writers = _acl_writers(path, metadata)
    if writers:
        raise UntrustedTreeError(errno.EACCES, "{}: {}".format(path, "; ".join(writers)))


def require_private_tree(path):
    """Refuse (`PermissionError`) a directory tree a script builds and runs
    a checker from unless no other user can change anything in it, and
    return its canonical path (`require_private`'s contract).

    The directory itself must pass `canonical_owner_private_directory` (its
    canonical ancestors included; an ancestor's refusal is a plain
    `PermissionError`, one of the tree's own entries an
    `UntrustedTreeError`). Then every entry below it is judged, each
    directory before it is listed, so no listing can change after it was
    read: a directory or regular file must be owned by this effective user
    with no group/other write bit; a symlink is accepted only when its
    resolution never leaves the tree, hop by hop through its literal target
    (`_symlink_stays_in_tree`; every position it visits is an entry the walk
    judges); anything else (a FIFO, socket or device) is refused. Read and
    execute bits are allowed. Nothing is changed. Hard links need no rule: a
    file no other user can write is unchanged whichever name reaches it.

    The root and every directory and regular file below it must also have
    no POSIX access ACL, and no directory a default ACL, that lets anyone
    but this user write (`_acl_writers`, read by scripts/host_boundary.py's
    reader): a default ACL decides who can write what is created in the
    directory later, whatever the umask, so the soundness gate's check of
    an existing pinned checkout before anything is built in it refuses one
    (X-HOST-P13 round-4 verifier; LD-75 repair)."""
    root = os.path.realpath(os.fspath(path))
    _check_canonical_ancestors(root)
    try:
        check_owner_private(root, True)
    except PermissionError as error:
        raise UntrustedTreeError(error.errno, error.strerror) from error
    _refuse_acl_writers(root, os.lstat(root))
    euid = os.geteuid()
    pending = [root]
    while pending:
        directory = pending.pop()
        with os.scandir(directory) as entries:
            names = [entry.name for entry in entries]
        for name in names:
            entry = os.path.join(directory, name)
            metadata = os.lstat(entry)
            if stat.S_ISLNK(metadata.st_mode):
                if not _symlink_stays_in_tree(root, entry):
                    raise UntrustedTreeError(errno.EACCES, "{} is a symlink to {!r}, whose resolution leaves the "
                                             "tree".format(entry, os.readlink(entry)))
                continue
            if not (stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)):
                raise UntrustedTreeError(errno.EACCES, "{} is neither a directory, a regular file nor a symlink".format(
                    entry))
            if metadata.st_uid != euid:
                raise UntrustedTreeError(errno.EACCES, "{} is owned by uid {}, not the effective uid {}".format(
                    entry, metadata.st_uid, euid))
            if metadata.st_mode & 0o022:
                raise UntrustedTreeError(errno.EACCES, "{} has mode {:04o}; another user could replace its contents".format(
                    entry, _mode(metadata)))
            _refuse_acl_writers(entry, metadata)
            if stat.S_ISDIR(metadata.st_mode):
                pending.append(entry)
    return root


class ExportError(Exception):
    """`export_commit_paths` refused: the export does not hold exactly the
    commit's bytes, or cannot be made."""


# The environment git runs in for an export: none of the caller's GIT_*
# variables (an object directory, alternates, a replacement config), no
# system or global configuration (whose attributes and filters `git archive`
# applied: X-HOST-P13 sixth closure audit), no replace refs, no prompt.
def _export_git_environment():
    environment = {name: value for name, value in os.environ.items() if not name.startswith("GIT_")}
    environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_NO_REPLACE_OBJECTS="1",
                       GIT_ATTR_NOSYSTEM="1", GIT_TERMINAL_PROMPT="0", GIT_NO_LAZY_FETCH="1", LC_ALL="C")
    return environment


# Options that keep every configured program and attribute out of the export's
# git commands, whatever the repository's own configuration says.
EXPORT_GIT_OPTIONS = ["-c", "core.attributesFile=" + os.devnull, "-c", "core.fsmonitor=false",
                      "-c", "core.hooksPath=" + os.devnull]


def _object_hash(algorithm, kind, data):
    import hashlib
    digest = hashlib.new(algorithm)
    digest.update("{} {}\0".format(kind, len(data)).encode())
    digest.update(data)
    return digest.hexdigest()


class _ObjectReader:
    """`git cat-file --batch` over one repository: every object read is
    hashed again here and must hash to the name it was asked by, so the
    bytes are the commit's whatever the object store holds."""

    def __init__(self, repo, algorithm):
        import subprocess
        self.algorithm = algorithm
        self.process = subprocess.Popen(["git"] + EXPORT_GIT_OPTIONS + ["-C", repo, "cat-file", "--batch"],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.DEVNULL, env=_export_git_environment())

    def read(self, oid, kind):
        self.process.stdin.write(oid.encode() + b"\n")
        self.process.stdin.flush()
        header = self.process.stdout.readline().decode("ascii", "replace").split()
        if len(header) != 3 or header[0] != oid:
            raise ExportError("the object store has no object {} ({})".format(oid, " ".join(header) or "no answer"))
        size = int(header[2])
        data = self.process.stdout.read(size)
        self.process.stdout.read(1)
        if header[1] != kind or len(data) != size:
            raise ExportError("object {} is a {}, not a {}".format(oid, header[1], kind))
        if _object_hash(self.algorithm, kind, data) != oid:
            raise ExportError("object {} read from the object store does not hash to its name".format(oid))
        return data

    def close(self):
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.wait()


def _tree_entries(data, width):
    """The (mode, name, oid) entries of a raw tree object."""
    entries = []
    index = 0
    while index < len(data):
        space = data.index(b" ", index)
        nul = data.index(b"\0", space)
        mode = data[index:space].decode("ascii")
        name = data[space + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 1 + width].hex()
        entries.append((mode, name, oid))
        index = nul + 1 + width
    return entries


def _blob_hash_of_file(algorithm, path):
    with open(path, "rb") as handle:
        return _object_hash(algorithm, "blob", handle.read())


def verify_export(destination, expected, algorithm):
    """Read the export at `destination` back: its entries must be exactly
    `expected` (relative path -> blob name, or None for a directory), every
    directory a directory, every file an owner-only regular file whose bytes,
    as written, hash to its blob. Refuses (`ExportError`) otherwise."""
    found = {}
    for current, directories, files in os.walk(destination):
        relative_dir = os.path.relpath(current, destination)
        for name in directories + files:
            relative = name if relative_dir == os.curdir else relative_dir + "/" + name
            found[relative] = os.path.join(current, name)
    if set(found) != set(expected):
        extra = sorted(set(found) - set(expected))
        missing = sorted(set(expected) - set(found))
        raise ExportError("the export's entries are not the commit's (extra {}, missing {})".format(
            extra[:5], missing[:5]))
    for relative, blob in sorted(expected.items()):
        metadata = os.lstat(found[relative])
        if blob is None:
            if not stat.S_ISDIR(metadata.st_mode):
                raise ExportError("{} is not a directory in the export".format(relative))
            continue
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_mode & 0o077:
            raise ExportError("{} is not an owner-only regular file in the export".format(relative))
        if _blob_hash_of_file(algorithm, found[relative]) != blob:
            raise ExportError("{} as written does not hash to its blob {}".format(relative, blob))


def export_commit_paths(repo, commit, destination, paths):
    """Write the directories `paths` of `commit` in the repository at `repo`
    into the new directory `destination`, from the object store by hash,
    and return the canonical `destination`.

    The commit object and every tree and blob are read with `git cat-file
    --batch` in `_export_git_environment` (no system or global
    configuration, no attributes, no filters, no replace refs) and each is
    hashed again here: the commit must hash to `commit`, each tree and blob
    to the name its parent tree gives it. Files are created exclusively,
    owner-only (0600; 0700 for an executable blob), in directories made 0700
    whatever the umask. Afterwards the export is read back: the set of its
    entries must be exactly the trees' entries, and every file's bytes must
    hash to its blob. Only regular files and directories are exported; a
    symlink or submodule entry is refused. Refuses (`ExportError`) on any
    difference."""
    import subprocess
    if len(commit) not in (40, 64) or any(char not in "0123456789abcdef" for char in commit):
        raise ExportError("{!r} is not a full object name".format(commit))
    algorithm = "sha1" if len(commit) == 40 else "sha256"
    width = len(commit) // 2
    if os.path.lexists(destination):
        raise ExportError("{} already exists".format(destination))
    if not create_private_dir_all(destination):
        raise ExportError("{} was not created by this export".format(destination))
    reader = _ObjectReader(repo, algorithm)
    expected = {}
    try:
        commit_data = reader.read(commit, "commit")
        first = commit_data.split(b"\n", 1)[0].decode("ascii", "replace").split()
        if len(first) != 2 or first[0] != "tree":
            raise ExportError("commit {} names no tree".format(commit))
        root_tree = first[1]
        for wanted in paths:
            parts = [part for part in wanted.split("/") if part]
            oid = root_tree
            for depth, part in enumerate(parts):
                found = [entry for entry in _tree_entries(reader.read(oid, "tree"), width) if entry[1] == part]
                if len(found) != 1 or found[0][0] != "40000":
                    raise ExportError("{} is not a directory of commit {}".format("/".join(parts[:depth + 1]), commit))
                oid = found[0][2]
            pending = [(oid, "/".join(parts))]
            while pending:
                tree, relative = pending.pop()
                directory = os.path.join(destination, relative)
                create_private_dir_all(directory)
                expected[relative] = None
                for mode, name, child in _tree_entries(reader.read(tree, "tree"), width):
                    if name in ("", ".", "..") or "/" in name:
                        raise ExportError("tree {} holds the entry name {!r}".format(tree, name))
                    child_relative = relative + "/" + name
                    if mode == "40000":
                        pending.append((child, child_relative))
                    elif mode in ("100644", "100755"):
                        data = reader.read(child, "blob")
                        file_mode = 0o700 if mode == "100755" else PRIVATE_FILE_MODE
                        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0) \
                            | getattr(os, "O_CLOEXEC", 0)
                        with private_umask():
                            descriptor = os.open(os.path.join(destination, child_relative), flags, file_mode)
                        with os.fdopen(descriptor, "wb") as handle:
                            os.fchmod(handle.fileno(), file_mode)
                            handle.write(data)
                        expected[child_relative] = child
                    else:
                        raise ExportError("{} has mode {} (only regular files and directories are exported)".format(
                            child_relative, mode))
            # Every directory above an exported path is part of the export.
            for depth in range(1, len(parts)):
                expected.setdefault("/".join(parts[:depth]), None)
    finally:
        reader.close()
    verify_export(destination, expected, algorithm)
    # Cross-check the walk against git's own listing of the same paths.
    listing = subprocess.Popen(["git"] + EXPORT_GIT_OPTIONS + ["-C", repo, "ls-tree", "-r", "-z", "--full-tree",
                                                                commit, "--"] + list(paths),
                               stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=_export_git_environment())
    out, _ = listing.communicate()
    listed = {}
    for record in out.split(b"\0"):
        if not record:
            continue
        meta, _, name = record.partition(b"\t")
        fields = meta.decode("ascii", "replace").split()
        if len(fields) == 3:
            listed[name.decode("utf-8", "surrogateescape")] = fields[2]
    blobs = {relative: blob for relative, blob in expected.items() if blob is not None}
    if listing.returncode != 0 or listed != blobs:
        raise ExportError("`git ls-tree -r {}` does not list exactly the exported blobs".format(commit))
    return os.path.realpath(destination)


def main(argv):
    if argv[:1] == ["export-commit"]:
        if len(argv) < 5:
            print("usage: private_cache.py export-commit REPO COMMIT DESTINATION PATH [PATH ...]", file=sys.stderr)
            return 2
        try:
            canonical = export_commit_paths(argv[1], argv[2], argv[3], argv[4:])
        except (ExportError, OSError, ValueError) as error:
            print("private_cache: export of {} refused: {}".format(argv[2], error), file=sys.stderr)
            return 1
        sys.stdout.buffer.write(os.fsencode(canonical) + b"\n")
        return 0
    if argv == ["cache-base"]:
        try:
            print(user_cache_base())
        except ValueError as error:
            print("private_cache: no user cache: {}".format(error), file=sys.stderr)
            return 1
        return 0
    if len(argv) < 2 or argv[0] not in ("mkdir", "require-private", "require-private-tree"):
        print("usage: private_cache.py mkdir DIR [DIR ...] | cache-base | require-private PATH [PATH ...] "
              "| require-private-tree DIR [DIR ...]", file=sys.stderr)
        return 2
    for path in argv[1:]:
        if argv[0] in ("require-private", "require-private-tree"):
            tree = argv[0] == "require-private-tree"
            try:
                canonical = require_private_tree(path) if tree else require_private(path)
            except OSError as error:
                remedy = TREE_REMEDY if isinstance(error, UntrustedTreeError) else PRIVATE_REMEDY
                print("private_cache: refusing {}: {}; {}".format(path, error.strerror or error, remedy),
                      file=sys.stderr)
                return 1
            if "\n" in canonical:
                # One path per line: a shell caller could not take this one
                # back whole, and running a truncated name is running another
                # path than the one checked.
                print("private_cache: refusing {!r}: its canonical path holds a newline".format(path),
                      file=sys.stderr)
                return 1
            # The path's own bytes, whatever the locale's encoding.
            sys.stdout.flush()
            sys.stdout.buffer.write(os.fsencode(canonical) + b"\n")
            sys.stdout.buffer.flush()
            continue
        try:
            create_private_dir_all(path)
        except OSError as error:
            print("private_cache: cannot create {}: {}".format(path, error), file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
