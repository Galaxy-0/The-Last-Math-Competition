import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

noncomputable section
namespace Conjecture257

/-- The positive imaginary square root of `-d` in the complex numbers. -/
def imaginaryRoot (d : ℕ) : ℂ := (Real.sqrt (d : ℝ) : ℂ) * Complex.I

/-- The field Q(sqrt(-d)), as an actual subfield of the complex numbers. -/
def quadraticField (d : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {imaginaryRoot d}

theorem imaginaryRoot_sq (d : ℕ) : imaginaryRoot d ^ 2 = -(d : ℂ) := by
  rw [imaginaryRoot, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

theorem imaginaryRoot_integral (d : ℕ) : IsIntegral ℚ (imaginaryRoot d) := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [imaginaryRoot_sq]
  simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := -(d : ℚ)))

instance quadraticFieldNumberField (d : ℕ) : NumberField (quadraticField d) where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (imaginaryRoot_integral d)

/-- The root has strictly positive imaginary part when d is positive. -/
theorem imaginaryRoot_im_pos (d : ℕ) (hd : 0 < d) : 0 < (imaginaryRoot d).im := by
  simpa [imaginaryRoot] using Real.sqrt_pos.mpr (show (0 : ℝ) < d by exact_mod_cast hd)

/-- The defining quadratic is irreducible over Q for every positive d. -/
theorem definingPolynomial_irreducible (d : ℕ) (hd : 0 < d) :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Polynomial.natDegree_X_pow_add_C]
    norm_num
  · intro x hx
    have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
    have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa [Polynomial.IsRoot] using hx
    nlinarith [sq_nonneg x]

/-- The chosen field has degree exactly two over Q for positive d. -/
theorem quadraticField_finrank (d : ℕ) (hd : 0 < d) :
    Module.finrank ℚ (quadraticField d) = 2 := by
  change Module.finrank ℚ (IntermediateField.adjoin ℚ {imaginaryRoot d}) = 2
  rw [IntermediateField.adjoin.finrank (imaginaryRoot_integral d)]
  have hp : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ (imaginaryRoot d) := by
    apply minpoly.eq_of_irreducible_of_monic (definingPolynomial_irreducible d hd)
    · simp [imaginaryRoot_sq]
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  rw [← hp]
  exact Polynomial.natDegree_X_pow_add_C

/-- Class number of the full ring of integers of Q(sqrt(-d)). -/
def imaginaryClassNumber (d : ℕ) : ℕ := NumberField.classNumber (quadraticField d)

theorem imaginaryRoot_mul_square (d m : ℕ) :
    imaginaryRoot (d * m ^ 2) = (m : ℂ) * imaginaryRoot d := by
  simp only [imaginaryRoot, Nat.cast_mul, Nat.cast_pow]
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (Nat.cast_nonneg m)]
  push_cast
  ring

theorem quadraticField_mul_square (d m : ℕ) (hm : m ≠ 0) :
    quadraticField (d * m ^ 2) = quadraticField d := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    rw [imaginaryRoot_mul_square]
    apply mul_mem
    · exact (quadraticField d).natCast_mem m
    · exact IntermediateField.subset_adjoin ℚ {imaginaryRoot d} (by simp)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hmem : imaginaryRoot (d * m ^ 2) ∈ quadraticField (d * m ^ 2) :=
      IntermediateField.subset_adjoin ℚ {imaginaryRoot (d * m ^ 2)} (by simp)
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have heq : imaginaryRoot d = imaginaryRoot (d * m ^ 2) / (m : ℂ) := by
      rw [imaginaryRoot_mul_square]
      field_simp
    rw [heq]
    exact div_mem hmem ((quadraticField (d * m ^ 2)).natCast_mem m)

/-- Equality of embedded number fields preserves the standard class number. -/
theorem classNumber_congr (K L : IntermediateField ℚ ℂ)
    [NumberField K] [NumberField L] (h : K = L) :
    NumberField.classNumber K = NumberField.classNumber L := by
  subst L
  rfl

theorem imaginaryClassNumber_mul_square (d m : ℕ) (hm : m ≠ 0) :
    imaginaryClassNumber (d * m ^ 2) = imaginaryClassNumber d := by
  unfold imaginaryClassNumber
  exact classNumber_congr _ _ (quadraticField_mul_square d m hm)

/-- Elementary negative Pell solutions with no upper bound on the first coordinate. -/
theorem pell_unbounded (k : ℕ) :
    ∃ n m : ℕ, k < n ∧ 0 < m ∧ n ^ 2 + 1 = 2 * m ^ 2 := by
  induction k with
  | zero => exact ⟨1, 1, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨n, m, hn, hm, heq⟩ := ih
    refine ⟨3 * n + 4 * m, 2 * n + 3 * m, ?_, ?_, ?_⟩
    · omega
    · omega
    · nlinarith

/-- Every proposed positive constant fails for some integer n at least two. -/
theorem counterexample_for_every_constant (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, 2 ≤ n ∧
      (imaginaryClassNumber (n ^ 2 + 1) : ℝ) < c * Real.log (n : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.exp ((imaginaryClassNumber 2 : ℝ) / c))
  obtain ⟨n, m, hn, hm, heq⟩ := pell_unbounded (k + 2)
  refine ⟨n, by omega, ?_⟩
  rw [heq, imaginaryClassNumber_mul_square 2 m (Nat.ne_of_gt hm)]
  have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast (show k < n by omega)
  have hexp : Real.exp ((imaginaryClassNumber 2 : ℝ) / c) < (n : ℝ) := hk.trans hkn
  have hlog := Real.log_lt_log (Real.exp_pos ((imaginaryClassNumber 2 : ℝ) / c)) hexp
  rw [Real.log_exp] at hlog
  exact (div_lt_iff₀ hc).mp hlog |>.trans_eq (mul_comm _ _)

/-- The quantified conjecture, using the natural logarithm. -/
def Conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    c * Real.log (n : ℝ) ≤ (imaginaryClassNumber (n ^ 2 + 1) : ℝ)

/-- Disproof is stronger than the failure to find an explicit constant: none exists. -/
theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨n, hn, hfail⟩ := counterexample_for_every_constant c hc
  exact (not_lt_of_ge (hbound n hn)) hfail

end Conjecture257
