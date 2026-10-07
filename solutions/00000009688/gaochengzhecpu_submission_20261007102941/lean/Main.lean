import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial
open scoped Real

namespace Conjecture9688

/-- An ordinary exponential polynomial with rational coefficients and natural exponents. -/
def expPoly (p : ℚ[X]) (z : ℂ) : ℂ := p.eval₂ (algebraMap ℚ ℂ) (Complex.exp z)

def f : ℚ[X] := X - 1
def g : ℚ[X] := X ^ 3 - X ^ 2
def h : ℚ[X] := X ^ 3 + X ^ 2

theorem f_support : f.support = {0, 1} := by
  ext n
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;>
    simp [f, Polynomial.mem_support_iff, coeff_X, coeff_one, h0, h1, eq_comm]
theorem g_support : g.support = {2, 3} := by
  ext n
  by_cases h2 : n = 2 <;> by_cases h3 : n = 3 <;>
    simp [g, Polynomial.mem_support_iff, coeff_X_pow, h2, h3]
theorem h_support : h.support = {2, 3} := by
  ext n
  by_cases h2 : n = 2 <;> by_cases h3 : n = 3 <;>
    simp [h, Polynomial.mem_support_iff, coeff_X_pow, h2, h3]

theorem supports_disjoint : Disjoint f.support g.support ∧ Disjoint f.support h.support := by
  rw [f_support, g_support, h_support]
  decide

theorem f_nonzero : f ≠ 0 := by
  intro hz
  have hs := congrArg Polynomial.support hz
  rw [f_support] at hs
  norm_num at hs

theorem g_nonzero : g ≠ 0 := by
  intro hz
  have hs := congrArg Polynomial.support hz
  rw [g_support] at hs
  norm_num at hs

theorem h_nonzero : h ≠ 0 := by
  intro hz
  have hs := congrArg Polynomial.support hz
  rw [h_support] at hs
  norm_num at hs

theorem f_formula (z : ℂ) : expPoly f z = Complex.exp z - 1 := by
  simp [expPoly, f]

theorem g_formula (z : ℂ) :
    expPoly g z = Complex.exp (3 * z) - Complex.exp (2 * z) := by
  simpa [expPoly, g] using
    congrArg₂ (fun a b : ℂ => a - b) (Complex.exp_nat_mul z 3).symm
      (Complex.exp_nat_mul z 2).symm

theorem h_formula (z : ℂ) :
    expPoly h z = Complex.exp (3 * z) + Complex.exp (2 * z) := by
  simpa [expPoly, h] using
    congrArg₂ (fun a b : ℂ => a + b) (Complex.exp_nat_mul z 3).symm
      (Complex.exp_nat_mul z 2).symm

theorem g_factor (z : ℂ) : expPoly g z = Complex.exp z ^ 2 * expPoly f z := by
  simp [expPoly, f, g]
  ring

def commonZeros (p q : ℚ[X]) : Set ℂ := {z | expPoly p z = 0 ∧ expPoly q z = 0}

def zeroAt (k : ℤ) : ℂ := k * (2 * Real.pi * Complex.I)

theorem zeroAt_common (k : ℤ) : zeroAt k ∈ commonZeros f g := by
  have he : Complex.exp (zeroAt k) = 1 := Complex.exp_int_mul_two_pi_mul_I k
  simp [commonZeros, expPoly, f, g, he]

theorem zeroAt_injective : Function.Injective zeroAt := by
  intro k l hkl
  have hn : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hc : (k : ℂ) = (l : ℂ) := (mul_left_inj' hn).mp hkl
  exact_mod_cast hc

theorem infinitely_many_common_zeros : (commonZeros f g).Infinite := by
  apply (Set.infinite_range_of_injective zeroAt_injective).mono
  rintro z ⟨k, rfl⟩
  exact zeroAt_common k

theorem h_eq_two_at_f_zero {z : ℂ} (hz : expPoly f z = 0) : expPoly h z = 2 := by
  have he : Complex.exp z = 1 := sub_eq_zero.mp ((f_formula z) ▸ hz)
  norm_num [expPoly, h, he]

theorem no_common_zeros : commonZeros f h = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  have he := h_eq_two_at_f_zero hz.1
  have : (2 : ℂ) = 0 := he.symm.trans hz.2
  norm_num at this

theorem same_exponent_sets_different_zero_sets :
    g.support = h.support ∧ (commonZeros f g).Nonempty ∧ commonZeros f h = ∅ := by
  exact ⟨g_support.trans h_support.symm, ⟨zeroAt 0, zeroAt_common 0⟩, no_common_zeros⟩

/-- No formula using just the exponent-set intersection can give all common-zero counts. -/
theorem no_intersection_count_formula :
    ¬ ∃ count : Finset ℕ → ℕ∞, ∀ p q : ℚ[X], p ≠ 0 → q ≠ 0 →
      (commonZeros p q).encard = count (p.support ∩ q.support) := by
  rintro ⟨count, hc⟩
  have heq : (commonZeros f g).encard = (commonZeros f h).encard := by
    rw [hc f g f_nonzero g_nonzero, hc f h f_nonzero h_nonzero, g_support, h_support]
  rw [no_common_zeros, Set.encard_empty] at heq
  have hempty : commonZeros f g = ∅ := Set.encard_eq_zero.mp heq
  have hmem := zeroAt_common 0
  rw [hempty] at hmem
  exact hmem

/-- A positive distance between the two zero sets is impossible despite disjoint supports. -/
theorem no_positive_zero_separation :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ z w : ℂ,
      expPoly f z = 0 → expPoly g w = 0 → δ ≤ dist z w := by
  rintro ⟨δ, hδ, hsep⟩
  have hz := zeroAt_common 0
  have hd := hsep _ _ hz.1 hz.2
  rw [dist_self] at hd
  exact (not_le_of_gt hδ) hd

#print axioms f_support
#print axioms supports_disjoint
#print axioms g_formula
#print axioms h_formula
#print axioms infinitely_many_common_zeros
#print axioms no_common_zeros
#print axioms no_intersection_count_formula
#print axioms no_positive_zero_separation

end Conjecture9688
