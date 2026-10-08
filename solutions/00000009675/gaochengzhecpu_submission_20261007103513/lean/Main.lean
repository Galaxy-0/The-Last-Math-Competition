import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin
open Cardinal Algebra

namespace Conjecture9675

theorem two_generated_trdeg_le_two (v : Fin 2 → ℂ) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range v)) ≤ 2 := by
  let ev : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval v
  have hrange : Algebra.adjoin ℚ (Set.range v) = ev.range :=
    Algebra.adjoin_range_eq_range_aeval ℚ v
  have hring : Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range v)) ≤ 2 := by
    rw [hrange]
    calc
      Algebra.trdeg ℚ ev.range ≤ Algebra.trdeg ℚ (MvPolynomial (Fin 2) ℚ) :=
        trdeg_le_of_surjective ev.rangeRestrict ev.rangeRestrict_surjective
      _ = 2 := by simp [MvPolynomial.trdeg_of_isDomain]
  have htower := trdeg_add_eq ℚ (Algebra.adjoin ℚ (Set.range v))
    (A := IntermediateField.adjoin ℚ (Set.range v))
  rw [trdeg_eq_zero (R := Algebra.adjoin ℚ (Set.range v))
    (A := IntermediateField.adjoin ℚ (Set.range v)), add_zero] at htower
  exact htower ▸ hring

def gammaPair (N : ℕ) : Fin 2 → ℂ :=
  ![Complex.Gamma (1 / (N : ℂ)), Complex.Gamma (2 / (N : ℂ))]

def gammaField (N : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (gammaPair N))

theorem gammaField_trdeg_le_two (N : ℕ) : Algebra.trdeg ℚ (gammaField N) ≤ 2 :=
  two_generated_trdeg_le_two (gammaPair N)

theorem oneOhFive_prime_factors : Nat.primeFactors 105 = {3, 5, 7} := by
  have h7 : Nat.Prime 7 := by decide
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have he : 105 = 3 * (5 * 7) := by norm_num
  rw [he, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    h3.primeFactors, h5.primeFactors, h7.primeFactors]
  decide

theorem oneOhFive_has_three_prime_factors : 2 < (Nat.primeFactors 105).card := by
  rw [oneOhFive_prime_factors]
  decide

theorem oneOhFive_totient : Nat.totient 105 = 48 := by decide

theorem gamma_oneOhFive_degree_not_twenty_four : Algebra.trdeg ℚ (gammaField 105) ≠ 24 := by
  intro h
  have hb := gammaField_trdeg_le_two 105
  rw [h] at hb
  norm_num at hb

theorem oneOhFive_counterexample :
    7 ≤ (105 : ℕ) ∧ 2 < (Nat.primeFactors 105).card ∧
    Algebra.trdeg ℚ (gammaField 105) ≠ (Nat.totient 105 / 2 : ℕ) := by
  refine ⟨by norm_num, oneOhFive_has_three_prime_factors, ?_⟩
  simpa [oneOhFive_totient] using gamma_oneOhFive_degree_not_twenty_four

theorem conjectured_totient_clause_false :
    ¬ ∀ N : ℕ, 7 ≤ N → 2 < (Nat.primeFactors N).card →
      Algebra.trdeg ℚ (gammaField N) = (Nat.totient N / 2 : ℕ) := by
  intro h
  exact oneOhFive_counterexample.2.2 (h 105 oneOhFive_counterexample.1 oneOhFive_counterexample.2.1)

#print axioms two_generated_trdeg_le_two
#print axioms gammaField_trdeg_le_two
#print axioms oneOhFive_prime_factors
#print axioms oneOhFive_totient
#print axioms oneOhFive_counterexample
#print axioms conjectured_totient_clause_false

end Conjecture9675
