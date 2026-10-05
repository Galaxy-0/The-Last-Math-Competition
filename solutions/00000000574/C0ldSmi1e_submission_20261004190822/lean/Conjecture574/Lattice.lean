import Conjecture574.FlatDefs
import Conjecture574.KLCore
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

noncomputable section
open scoped BigOperators Polynomial
open Polynomial
namespace Conjecture574

/-- The empty flat. -/
def flatBottom : Flat := ⟨∅, Or.inl (by decide)⟩
/-- The full flat. -/
def flatTop : Flat := ⟨Finset.univ, Or.inr rfl⟩

/-- Explicit integer values of the Möbius function, checked by its incidence recurrence below. -/
def mobius (a b : Flat) : ℤ :=
  if a = b then 1
  else if ¬ a ≤ b then 0
  else if flatRank b - flatRank a = 1 then -1
  else if flatRank b - flatRank a = 2 then
    if flatRank a = 0 then 1 else 2
  else -3

theorem mobius_left_recurrence : ∀ a b : Flat,
    (∑ c ∈ interval a b, mobius a c) = if a = b then 1 else 0 := by decide

theorem mobius_right_recurrence : ∀ a b : Flat,
    (∑ c ∈ interval a b, mobius c b) = if a = b then 1 else 0 := by decide

/-- The characteristic polynomial obtained from the full interval Möbius sum. -/
def characteristic (a b : Flat) : ℤ[X] :=
  ∑ c ∈ interval a b, C (mobius a c) * X ^ (flatRank b - flatRank c)

/-- The proposed family, subsequently verified against every defining KL condition. -/
def candidateKL (a b : Flat) : ℤ[X] :=
  if flatRank b - flatRank a = 3 then 1 + 2 * X else 1

theorem flatRank_le_three (a : Flat) : flatRank a ≤ 3 := by
  exact Nat.min_le_left _ _

theorem characteristic_natDegree_le (a b : Flat) :
    (characteristic a b).natDegree ≤ 3 := by
  apply natDegree_sum_le_of_forall_le
  intro c _
  exact (natDegree_C_mul_X_pow_le _ _).trans
    ((Nat.sub_le _ _).trans (flatRank_le_three b))

theorem candidateKL_natDegree_le (a b : Flat) : (candidateKL a b).natDegree ≤ 1 := by
  unfold candidateKL
  split_ifs
  · compute_degree
  · simp

theorem candidateKL_reflect (a b : Flat) :
    reflect (flatRank b-flatRank a) (candidateKL a b) =
    if flatRank b-flatRank a=3 then X^3+2*X^2 else X^(flatRank b-flatRank a) := by
  unfold candidateKL
  split_ifs with h
  · rw [h]
    have hx : (2 : ℤ[X])*X = C (2 : ℤ)*X^1 := by simp
    rw [hx, reflect_add, reflect_one, reflect_C_mul_X_pow]
    norm_num [revAt]
  · simp

theorem candidateKL_reflect_natDegree_le (a b : Flat) :
    (reflect (flatRank b-flatRank a) (candidateKL a b)).natDegree ≤ 4 := by
  rw [candidateKL_reflect]
  split_ifs
  · compute_degree; decide
  · simpa using (Nat.sub_le (flatRank b) (flatRank a)).trans
      ((flatRank_le_three b).trans (by decide : 3 ≤ 4))

theorem recurrence_rhs_natDegree_le (a b : Flat) :
    (∑ c ∈ interval a b, characteristic a c * candidateKL c b).natDegree ≤ 4 := by
  apply natDegree_sum_le_of_forall_le
  intro c _
  exact natDegree_mul_le.trans (Nat.add_le_add
    (characteristic_natDegree_le a c) (candidateKL_natDegree_le c b))

theorem characteristic_diagonal (a : Flat) : characteristic a a = 1 := by
  have hi : interval a a = {a} := by
    ext c
    simp only [mem_interval, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => by subst c; exact ⟨le_rfl, le_rfl⟩⟩
  simp [characteristic, hi, mobius]

theorem candidateKL_diagonal (a : Flat) : candidateKL a a = 1 := by
  simp [candidateKL]

theorem candidateKL_small (a b : Flat) (hab : a < b) :
    SmallDegree (flatRank b-flatRank a) (candidateKL a b) := by
  intro i hi
  have hr : flatRank a < flatRank b := flatRank_strictMono hab
  unfold candidateKL
  split_ifs with hd
  · have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    simp only [show (2 : ℤ[X]) = C 2 by simp, coeff_add, coeff_C_mul,
      coeff_one, coeff_X, hi0, hi1, Ne.symm hi1, if_false, mul_zero, zero_add]
  · have hi0 : i ≠ 0 := by omega
    simp only [coeff_one, hi0, if_false]

theorem polynomial_coeff_ite (p q : ℤ[X]) (h : Prop) [Decidable h] (i : ℕ) :
    (if h then p else q).coeff i = if h then p.coeff i else q.coeff i := by
  split_ifs <;> rfl

/-- Every coefficient needed to verify the recurrence, reduced to finite integer sums. -/
theorem candidateKL_recurrence_coeff : ∀ i : Fin 5, ∀ a b : Flat, a ≤ b →
    (reflect (flatRank b-flatRank a) (candidateKL a b)).coeff i =
    (∑ c ∈ interval a b, characteristic a c * candidateKL c b).coeff i := by
  intro i
  fin_cases i <;>
    simp only [candidateKL_reflect] <;>
    simp only [candidateKL, characteristic, show (2 : ℤ[X]) = C 2 by simp,
      coeff_C_mul, coeff_mul_C, mul_ite, mul_add, mul_one, ← mul_assoc,
      finset_sum_coeff, polynomial_coeff_ite, coeff_add, coeff_mul_X_zero,
      coeff_mul_X, coeff_C_mul_X_pow, coeff_X_pow] <;>
    decide

theorem candidateKL_recurrence (a b : Flat) (hab : a ≤ b) :
    reflect (flatRank b-flatRank a) (candidateKL a b) =
    ∑ c ∈ interval a b, characteristic a c * candidateKL c b := by
  apply (ext_iff_natDegree_le (candidateKL_reflect_natDegree_le a b)
    (recurrence_rhs_natDegree_le a b)).mpr
  intro i hi
  exact candidateKL_recurrence_coeff ⟨i, by omega⟩ a b hab

/-- The family satisfies all defining EPW axioms, on all intervals. -/
theorem candidateKL_isKL : IsKLFamily flatRank characteristic candidateKL :=
  ⟨candidateKL_diagonal, candidateKL_small, candidateKL_recurrence⟩

instance flatLocallyFiniteOrder : LocallyFiniteOrder Flat := Fintype.toLocallyFiniteOrder

theorem interval_eq_Icc (a b : Flat) : interval a b = Finset.Icc a b := by
  ext c
  simp

/-- The certified values, viewed as an element of the genuine incidence algebra. -/
def mobiusIncidence : IncidenceAlgebra ℤ Flat :=
  ⟨mobius, fun a b hab => by
    have hne : a ≠ b := fun h => hab (le_of_eq h)
    simp [mobius, hne, hab]⟩

theorem mobiusIncidence_mul_zeta :
    mobiusIncidence * IncidenceAlgebra.zeta ℤ = 1 := by
  ext a b hab
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply]
  calc
    ∑ c ∈ Finset.Icc a b, mobiusIncidence a c * IncidenceAlgebra.zeta ℤ c b =
        ∑ c ∈ Finset.Icc a b, mobius a c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [IncidenceAlgebra.zeta_of_le (Finset.mem_Icc.mp hc).2, mul_one]
      rfl
    _ = if a = b then 1 else 0 := by
      rw [← interval_eq_Icc]
      exact mobius_left_recurrence a b

/-- The computed function is Mathlib's recursively defined Möbius function. -/
theorem mobius_eq_incidence_mu (a b : Flat) :
    mobius a b = IncidenceAlgebra.mu ℤ a b := by
  have h : mobiusIncidence = (IncidenceAlgebra.mu ℤ : IncidenceAlgebra ℤ Flat) := by
    calc
      mobiusIncidence = mobiusIncidence * 1 := (mul_one _).symm
      _ = mobiusIncidence * (IncidenceAlgebra.zeta ℤ * IncidenceAlgebra.mu ℤ) := by
        rw [IncidenceAlgebra.zeta_mul_mu]
      _ = (mobiusIncidence * IncidenceAlgebra.zeta ℤ) * IncidenceAlgebra.mu ℤ :=
        (mul_assoc _ _ _).symm
      _ = IncidenceAlgebra.mu ℤ := by rw [mobiusIncidence_mul_zeta, one_mul]
  exact congrArg (fun f : IncidenceAlgebra ℤ Flat => f a b) h

theorem characteristic_eq_incidence_sum (a b : Flat) :
    characteristic a b = ∑ c ∈ Finset.Icc a b,
      C (IncidenceAlgebra.mu ℤ a c) * X^(flatRank b-flatRank c) := by
  simp only [characteristic, interval_eq_Icc, mobius_eq_incidence_mu]

/-- The whole-lattice characteristic polynomial, computed from its Möbius sum. -/
theorem characteristic_bottom_top :
    characteristic flatBottom flatTop = X^3 - 4*X^2 + 6*X - 3 := by
  have hd : (X^3 - 4*X^2 + 6*X - 3 : ℤ[X]).natDegree ≤ 3 := by compute_degree
  apply (ext_iff_natDegree_le (characteristic_natDegree_le _ _) hd).mpr
  have hc : ∀ i : Fin 4,
      (characteristic flatBottom flatTop).coeff i =
      (X^3 - 4*X^2 + 6*X - 3 : ℤ[X]).coeff i := by
    intro i
    fin_cases i <;>
      simp only [characteristic, finset_sum_coeff, coeff_C_mul_X_pow,
        show (4 : ℤ[X]) = C 4 by simp, show (6 : ℤ[X]) = C 6 by simp,
        show (3 : ℤ[X]) = C 3 by simp, coeff_add, coeff_sub, coeff_C_mul,
        coeff_C, coeff_X_pow, coeff_X] <;>
      decide
  intro i hi
  exact hc ⟨i, by omega⟩

theorem candidateKL_bottom_top : candidateKL flatBottom flatTop = 1 + 2*X := by
  simp [candidateKL, flatBottom, flatTop, flatRank]

end Conjecture574
