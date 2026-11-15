# Calling-frame foundation integrated with current main

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Source `98750d9c6afbec633d8e63712df282fbc10433a8` merges the earlier test-only foundation `b4238702` with
main `0dd7a110`. The source merged automatically; the generated inventory
conflict was resolved with the maintained documentation writer and checker.
The full incoming diff whitespace check refused trailing spaces in inherited
archived logs and patches. Those original records are preserved; the scoped
source/inventory diff check passed.

On Linux AArch64, all 25 selected `source_bound_frame::` tests pass, with zero
failures or ignored tests and 3,921 filtered tests. Stock Rust 1.97.1, two Cargo
jobs, exclusive host lease, 16 GiB RSS watchdog with zero grace. The retained
request identifies every source input and the frozen AY/Clean executables;
all inputs remained unchanged and no resource ceiling was breached.

The calling-cell checker remains behind `cfg(test)`. This integration grants
no new production foreign-call authority. Callee contracts, private storage
ownership/no-escape, source-to-byte composition, and the full Linux L01-L14
completion requirements remain open. This is not a Trust-certified build.
