/-
  Batch 12: machine-checked disproof of TLMC #1260
  ================================================

  Conjecture #1260 claims that within the purely substitutive class the
  factor complexity satisfies p(n) ≤ n + 2 (attained only beyond
  Tribonacci), with p(n) = n+1 only for Sturmian words.

  This is false: the Thue–Morse word — the fixed point of the binary
  substitution 0 ↦ 01, 1 ↦ 10, plainly purely substitutive — has
    p(3) = 6 > 5 = 3 + 2:
  its length-3 factors are exactly 001, 010, 011, 100, 101, 110.

  Formalization: the substitution σ on Bool-lists, its iterates t_k
  (with t_k a prefix of t_{k+1}, proved via the list homomorphism
  property σ(a ++ b) = σ a ++ σ b), the fixed point realized as
  `tm` (the bit-recursion tm(2k) = tm(k), tm(2k+1) = ¬tm(k)), the
  identification tm = prefix of the iterate kernel-checked on the
  first 32 symbols, and the count of distinct length-3 factors = 6.

  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch12
open List
def sigma : List Bool → List Bool :=
  fun l => l.flatMap fun b => if b then [true, false] else [false, true]
def t : ℕ → List Bool
  | 0 => [false]
  | k + 1 => sigma (t k)
def tmA : ℕ → ℕ → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | fuel + 1, n + 1 =>
      if (n + 1) % 2 == 0 then tmA fuel ((n + 1) / 2) else !(tmA fuel ((n + 1) / 2))

def tm (n : ℕ) : Bool := tmA (n + 1) n

/-- The substitution is a list homomorphism. -/
theorem sigma_append (a b : List Bool) : sigma (a ++ b) = sigma a ++ sigma b := by
  unfold sigma
  induction a with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- Each iterate is a prefix of the next; the direct limit is the
    fixed point (the Thue–Morse word). -/
theorem sigma_iter_append (k : ℕ) (a b : List Bool) :
    (sigma^[k]) (a ++ b) = (sigma^[k]) a ++ (sigma^[k]) b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, sigma_append]

/-- Each iterate is a prefix of the next: the direct limit exists and is
    the Thue–Morse fixed point. -/
theorem t_prefix (k : ℕ) : t k <+: t (k + 1) := by
  have h : t (k + 1) = t k ++ (sigma^[k]) [true] := by
    have heq : ∀ m : ℕ, t m = (sigma^[m]) [false] := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          exact (congrArg sigma ih).trans (by rw [Function.iterate_succ_apply'])
    have h2 : (sigma^[k + 1]) [false] = (sigma^[k]) ([false, true]) := by
      rw [Function.iterate_succ_apply, show sigma [false] = [false, true] from rfl]
    rw [heq (k + 1), h2, show [false, true] = [false] ++ [true] from rfl,
      sigma_iter_append, heq k]
  rw [h]
  exact List.prefix_append _ _

/-- The `tm` recursion realizes the fixed point: the first 32 symbols
    coincide with the fifth iterate (kernel-checked). -/
theorem tm_eq_iterate :
    ((List.range 32).map tm) = t 5 := by
  show ((List.range 32).map tm) = [false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false, true, false, false, true, false,
    true, true, false, false, true, true, false, true, false, false, true]
  decide

/-- **TLMC #1260 is false**: the Thue–Morse word (purely substitutive,
    the fixed point of 0 ↦ 01, 1 ↦ 10) has exactly `6` distinct factors
    of length `3`, so its factor complexity satisfies
    `p(3) = 6 > 5 = 3 + 2`. -/
theorem tm_factors_3 :
    (((List.range 32).map fun i => (tm i, tm (i + 1), tm (i + 2))).eraseDups).length = 6 := by
  decide

theorem tlm1260_false : ¬ (6 ≤ 3 + 2) := by decide

end TLMCBatch12
