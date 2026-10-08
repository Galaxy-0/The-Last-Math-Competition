import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum

noncomputable section
open Cardinal Algebra
open scoped IntermediateField.algebraAdjoinAdjoin Real

namespace Conjecture9689

theorem finite_generated_trdeg_le (K : Type) [Field K] [Algebra K ℂ]
    (n : ℕ) (v : Fin n → ℂ) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range v)) ≤ n := by
  let ev : MvPolynomial (Fin n) K →ₐ[K] ℂ := MvPolynomial.aeval v
  have hrange : Algebra.adjoin K (Set.range v) = ev.range :=
    Algebra.adjoin_range_eq_range_aeval K v
  have hring : Algebra.trdeg K (Algebra.adjoin K (Set.range v)) ≤ n := by
    rw [hrange]
    calc
      Algebra.trdeg K ev.range ≤ Algebra.trdeg K (MvPolynomial (Fin n) K) :=
        trdeg_le_of_surjective ev.rangeRestrict ev.rangeRestrict_surjective
      _ = n := by simp [MvPolynomial.trdeg_of_isDomain]
  have htower := trdeg_add_eq K (Algebra.adjoin K (Set.range v))
    (A := IntermediateField.adjoin K (Set.range v))
  rw [trdeg_eq_zero (R := Algebra.adjoin K (Set.range v))
    (A := IntermediateField.adjoin K (Set.range v)), add_zero] at htower
  exact htower ▸ hring

def auxiliaryField (j : ℂ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {j}

def iteratedField (x j : ℂ) : IntermediateField (auxiliaryField j) ℂ :=
  IntermediateField.adjoin (auxiliaryField j) {x}

theorem iteratedField_eq (x j : ℂ) :
    (iteratedField x j).restrictScalars ℚ = IntermediateField.adjoin ℚ {x, j} := by
  simpa [iteratedField, auxiliaryField, Set.singleton_union, Set.pair_comm] using
    IntermediateField.adjoin_adjoin_left ℚ ({j} : Set ℂ) ({x} : Set ℂ)

theorem adjoining_algebraic_value_bound (x j : ℂ) (hj : IsAlgebraic ℚ j) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ ({x, j} : Set ℂ)) ≤ 1 := by
  letI : Algebra.IsAlgebraic ℚ (auxiliaryField j) :=
    IntermediateField.isAlgebraic_adjoin_simple hj.isIntegral
  have hbound : Algebra.trdeg (auxiliaryField j) (iteratedField x j) ≤ 1 := by
    have hsingle : Set.range (fun _ : Fin 1 => x) = ({x} : Set ℂ) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact Set.mem_singleton x
      · rintro rfl
        exact ⟨0, rfl⟩
    have hb := finite_generated_trdeg_le (auxiliaryField j) 1 (fun _ : Fin 1 => x)
    rw [hsingle] at hb
    exact hb
  have htower := trdeg_add_eq ℚ (auxiliaryField j) (A := iteratedField x j)
  rw [trdeg_eq_zero (R := ℚ) (A := auxiliaryField j), zero_add] at htower
  have h : Algebra.trdeg ℚ (iteratedField x j) ≤ 1 := htower ▸ hbound
  change Algebra.trdeg ℚ ((iteratedField x j).restrictScalars ℚ) ≤ 1 at h
  rw [iteratedField_eq x j] at h
  exact h

def gelfondValue (d : ℕ) : ℂ := Complex.exp (Real.pi * Real.sqrt (d : ℝ))

theorem gelfond_joint_degree_not_two (d : ℕ) (j : ℂ) (hj : IsAlgebraic ℚ j) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ ({gelfondValue d, j} : Set ℂ)) ≠ 2 := by
  intro heq
  have h := adjoining_algebraic_value_bound (gelfondValue d) j hj
  rw [heq] at h
  norm_num at h

theorem one_is_positive_squarefree : 0 < (1 : ℕ) ∧ Squarefree (1 : ℕ) := by norm_num

/-- No assignment of algebraic auxiliary values can satisfy even all singleton cases. -/
theorem no_algebraic_auxiliary_assignment :
    ¬ ∃ J : ℕ → ℂ,
      (∀ d : ℕ, 0 < d → Squarefree d → IsAlgebraic ℚ (J d)) ∧
      (∀ d : ℕ, 0 < d → Squarefree d →
        Algebra.trdeg ℚ (IntermediateField.adjoin ℚ ({gelfondValue d, J d} : Set ℂ)) = 2) := by
  rintro ⟨J, halg, hdegree⟩
  have hp := one_is_positive_squarefree
  exact gelfond_joint_degree_not_two 1 (J 1) (halg 1 hp.1 hp.2) (hdegree 1 hp.1 hp.2)

#print axioms finite_generated_trdeg_le
#print axioms iteratedField_eq
#print axioms adjoining_algebraic_value_bound
#print axioms gelfond_joint_degree_not_two
#print axioms one_is_positive_squarefree
#print axioms no_algebraic_auxiliary_assignment

end Conjecture9689
