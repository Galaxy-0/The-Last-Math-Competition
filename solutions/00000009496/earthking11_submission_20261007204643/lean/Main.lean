import Mathlib.FieldTheory.ChevalleyWarning

/-!
# Conjecture 00000009496: Chevalley–Warning divisibility

The variables are actual coordinates of a finite-dimensional vector over a
finite field, and `f` is a finite family of actual multivariate polynomials.
`Fintype.card` counts their common zeroes, without an auxiliary numerical
surrogate. The result applies in particular to the conjecture's prime field
with `K = ZMod p`, `σ = Fin n`, and `ι = Fin r`.
-/

open MvPolynomial

theorem conjecture_00000009496
    {K σ ι : Type*} [Fintype K] [Field K]
    [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq K]
    (p : ℕ) [CharP K p] (f : ι → MvPolynomial σ K)
    (hdeg : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card
      { x : σ → K // ∀ i : ι, eval x (f i) = 0 } := by
  exact char_dvd_card_solutions_of_fintype_sum_lt p hdeg

#print axioms conjecture_00000009496
#print axioms char_dvd_card_solutions_of_fintype_sum_lt
