import Lake
open Lake DSL

package trust where

-- No external `require`: the only external import is `Std.Tactic.BVDecide`, which is
-- bundled in Lean core's `Std` from >= v4.31.0 (see lean-toolchain). Pulling std4 from git
-- would force a moving v4.32.0-rc1 download that does not match the pinned toolchain.

@[default_target]
lean_lib Trust where
