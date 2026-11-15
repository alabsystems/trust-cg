-- Reverse-induction bound rule ("DecIV"): the fact LLVM 22 does not derive for
--   for i in (1..len).rev() { a[i] = a[i] - a[i - 1] }
-- IR shape after InstCombine (all values u64):
--   header:  p = phi [s, preheader], [p - 1, latch]      ; s = len
--            continue iff p >u b                         ; b = 1 for (1..len)
--   body:    i = p - 1 ; check i <u s ; check i - 1 <u s
-- The rule is the inductive invariant `p ≤ s` on the in-loop edge:
--   init: p = s, so p ≤ s                                   (inv_init)
--   exact decrement: p >u b implies p ≥ 1 (guard_pos), so the u64 decrement
--         is exact (dec_exact); write p = q + 1
--   step: the next header value q satisfies q ≤ s           (inv_step)
--   use:  i = q < s                                         (check_i)
--         with b = 1: p ≥ 2 (guard_pos at b = 1), p = r + 2, i - 1 = r < s (check_im1)
-- Wrapping is excluded by the guard alone (p >u b implies p ≠ 0), so unlike
-- LLVM's eq/ne rule no precondition relating b and s is needed.
-- Checked with `clean check` (Clean's prelude lacks Nat.le_succ and friends,
-- and its omega only closes goals that are definitionally a hypothesis, so the
-- steps are spelled with Nat.le constructors and Nat.le_trans).
-- Nat values model u64 values below 2^64.

theorem le_succ' (n : Nat) : n ≤ n + 1 := Nat.le.step Nat.le.refl

theorem one_le_succ (b : Nat) : 1 ≤ b + 1 := by
  induction b with
  | zero => exact Nat.le.refl
  | succ n ih => exact Nat.le.step ih

theorem two_le_succ_succ (b : Nat) : 2 ≤ b + 2 := by
  induction b with
  | zero => exact Nat.le.refl
  | succ n ih => exact Nat.le.step ih

-- guard: p >u b  ==>  p ≥ b + 1 ≥ 1 (p ≠ 0, so p - 1 does not wrap)
theorem guard_pos (b p : Nat) (hg : b + 1 ≤ p) : 1 ≤ p := Nat.le_trans (one_le_succ b) hg

-- guard at b = 1: p >u 1  ==>  p ≥ 2 (p - 2 does not wrap)
theorem guard_pos2 (p : Nat) (hg : 1 + 1 ≤ p) : 2 ≤ p := hg

theorem dec_exact (p : Nat) (h : 1 ≤ p) : p - 1 + 1 = p := by omega

theorem inv_init (s : Nat) : s ≤ s := Nat.le.refl

theorem inv_step (q s : Nat) (hinv : q + 1 ≤ s) : q ≤ s := Nat.le_trans (le_succ' q) hinv

theorem check_i (q s : Nat) (hinv : q + 1 ≤ s) : q < s := hinv

theorem check_im1 (r s : Nat) (hinv : r + 2 ≤ s) : r < s := Nat.le_trans (le_succ' (r + 1)) hinv
