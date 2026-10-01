/-
  Batch 7: machine-checked disproof of TLMC #578
  ==============================================

  Conjecture #578 concerns the "binomial matroid" bin(n, i), given by the
  i-subsets of {1,…,n} under symmetric difference — i.e. the binary matroid
  on the C(n,i) incidence vectors of weight i in F₂ⁿ (for i = 2 this is the
  graphic matroid M(K_n)).  It asserts that for all 2 ≤ i ≤ n−2 and m ≥ 1,
  the value χ_{n,i}(−m) of the characteristic polynomial is divisible by
  i!·(n−i)!.

  This is false already at the smallest case n = 4, i = 2:
    χ_{4,2}(t) = t³ − 6t² + 11t − 6   (= P_{K₄}(t)/t),
    χ_{4,2}(−4) = −210,  and  2!·(4−2)! = 4 does not divide 210.

  The characteristic polynomial is computed by Whitney's subset expansion
  χ_M(t) = Σ_{A ⊆ E} (−1)^{|A|} t^{r(E) − r(A)}, with r(A) the linear rank
  over F₂, itself computed as the maximum size of a linearly independent
  subfamily.  Everything is kernel-verified by `decide` over the 64 subsets
  and the 64 coefficient vectors.

  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch7

open Finset

/-- The six weight-2 vectors of `F₂⁴`, indexed by the two-subsets of
    `{0,1,2,3}` in lexicographic order (the edge set of `K₄`). -/
def vec : Fin 6 → (Fin 4 → ZMod 2) :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, 0, 1], ![0, 1, 1, 0], ![0, 1, 0, 1],
    ![0, 0, 1, 1]]

/-- All `2^6` coefficient vectors, enumerated by bits (computable). -/
def allC : List (Fin 6 → ZMod 2) :=
  (List.range 64).map fun n k => if n.testBit k.val then (1 : ZMod 2) else 0

/-- A subset of the ground set is linearly independent over `F₂`
    (brute-force check over all `2^6` coefficient vectors). -/
def linIndepB (T : Finset (Fin 6)) : Bool :=
  allC.all fun c =>
    !(((List.finRange 6).all fun j => decide (j ∈ T) || decide (c j = 0))
      && decide (∑ j, c j • vec j = 0)
      && (List.finRange 6).any fun j => decide (c j ≠ 0))

/-- Sanity checks of the independence tester (kernel-computed):
    the empty set, singletons, and `{v₀, v₁}` are independent, while
    `{v₀, v₁, v₃}` is dependent (`v₀ + v₁ = v₃`). -/
theorem linIndepB_sanity :
    linIndepB ∅ && linIndepB {0} && linIndepB {0, 1} && !linIndepB {0, 1, 3} := by
  decide

/-- All 64 subsets of the six-element ground set, enumerated by bitmasks
    (computable). -/
def subMasks : List (Finset (Fin 6)) :=
  (List.range 64).map fun n =>
    ((List.finRange 6).filter fun j => n.testBit j.val).toFinset

/-- The linear rank of a subset: the maximum size of an independent
    subfamily (the rank function of the binary matroid). -/
def rankOf (S : Finset (Fin 6)) : ℕ :=
  ((subMasks.filter fun T =>
      ((List.finRange 6).all fun j => !(decide (j ∈ T)) || decide (j ∈ S))
        && linIndepB T).map fun T => T.card).foldl max 0

/-- The characteristic polynomial of `bin(4,2)` via Whitney's subset
    expansion: the coefficient of `t^k`. -/
def chiCoeff (k : ℕ) : ℤ :=
  ((subMasks.filter fun S => decide (rankOf S ≤ 3 && (3 - rankOf S == k))).map
    fun S => if S.card % 2 == 0 then (1 : ℤ) else -1).foldl (· + ·) 0

/-- The full rank of the configuration is `3` (the even-weight subspace). -/
theorem rank_full : rankOf (Finset.univ : Finset (Fin 6)) = 3 := by decide

set_option maxRecDepth 20000000 in
/-- The characteristic polynomial of `bin(4,2)` is `t³ − 6t² + 11t − 6`
    (kernel-computed). -/
theorem chi_coeffs :
    chiCoeff 0 = -6 ∧ chiCoeff 1 = 11 ∧ chiCoeff 2 = -6 ∧ chiCoeff 3 = 1 := by
  decide

set_option maxRecDepth 4000000 in
/-- `χ_{4,2}(−4) = −210` (kernel-computed). -/
theorem chi_eval_neg4 :
    chiCoeff 0 * 1 + chiCoeff 1 * (-4) + chiCoeff 2 * 16 + chiCoeff 3 * (-64) = -210 := by
  decide

set_option maxRecDepth 4000000 in
/-- **TLMC #578 is false**: at `n = 4`, `i = 2`, `m = 4` the value
    `χ_{4,2}(−4) = −210` is not divisible by `i!·(n−i)! = 2!·2! = 4`. -/
theorem tlm578_false : ¬ ((2 * 2 : ℕ) ∣ 210) := by decide

/-- The packaged refutation data. -/
theorem tlm578 :
    rankOf univ = 3 ∧ chiCoeff 0 = -6 ∧ chiCoeff 1 = 11 ∧ chiCoeff 2 = -6 ∧
      chiCoeff 3 = 1 ∧
      chiCoeff 0 * 1 + chiCoeff 1 * (-4) + chiCoeff 2 * 16 + chiCoeff 3 * (-64) = -210 ∧
      ¬ ((2 * 2 : ℕ) ∣ 210) :=
  ⟨rank_full, chi_coeffs.1, chi_coeffs.2.1, chi_coeffs.2.2.1, chi_coeffs.2.2.2,
    chi_eval_neg4, tlm578_false⟩

end TLMCBatch7
