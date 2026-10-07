import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
open Filter Asymptotics

namespace Conjecture7866

def deviation (S : ℕ → ℝ) (n : ℕ) : ℝ := |Int.fract (S n) - (n : ℝ) / 2|

theorem deviation_nonneg (S : ℕ → ℝ) (n : ℕ) : 0 ≤ deviation S n := abs_nonneg _

theorem deviation_linear_lower (S : ℕ → ℝ) (n : ℕ) :
    (n : ℝ) / 2 - 1 < deviation S n := by
  have hf := Int.fract_lt_one (S n)
  have ha := neg_le_abs (Int.fract (S n) - (n : ℝ) / 2)
  dsimp [deviation]
  linarith

theorem deviation_upper (S : ℕ → ℝ) (n : ℕ) :
    deviation S n ≤ (n : ℝ) / 2 + 1 := by
  have h0 := Int.fract_nonneg (S n)
  have h1 := Int.fract_lt_one (S n)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def maximalDeviation {Ω : Type} (S : Ω → ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (fun ω => deviation (S ω) n))

theorem deviation_le_maximal {Ω : Type} (S : Ω → ℕ → ℝ) (ω : Ω) (n : ℕ) :
    deviation (S ω) n ≤ maximalDeviation S n := by
  apply le_csSup
  · exact ⟨(n : ℝ) / 2 + 1, by rintro _ ⟨ω', rfl⟩; exact deviation_upper (S ω') n⟩
  · exact Set.mem_range_self ω

theorem maximal_linear_lower {Ω : Type} [Nonempty Ω] (S : Ω → ℕ → ℝ) (n : ℕ) :
    (n : ℝ) / 2 - 1 < maximalDeviation S n := by
  let ω : Ω := Classical.choice inferInstance
  exact lt_of_lt_of_le (deviation_linear_lower (S ω) n) (deviation_le_maximal S ω n)

theorem not_bigO_sqrt_log_of_linear_lower (D : ℕ → ℝ)
    (hD : ∀ n : ℕ, (n : ℝ) / 2 - 1 < D n) :
    ¬ D =O[atTop] (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) := by
  intro hO
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound.bound
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (max 4 ((4 * C) ^ 2)))
  have hnN : N ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) hn.le)
  have hn4 : (4 : ℝ) < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnsq : (4 * C) ^ 2 < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hroot : 4 * C < Real.sqrt (n : ℝ) := (Real.lt_sqrt (by positivity)).2 hnsq
  have hrootpos : 0 < Real.sqrt (n : ℝ) := by positivity
  have hmul := mul_lt_mul_of_pos_right hroot hrootpos
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg n)
  have hlog : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (Real.log_le_self (Nat.cast_nonneg n))
  have hlarge : C * Real.sqrt (Real.log (n : ℝ)) < (n : ℝ) / 2 - 1 := by
    have hmul2 := mul_le_mul_of_nonneg_left hlog hC.le
    nlinarith
  have hb := hN n hnN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  have hle := le_abs_self (D n)
  have hd := hD n
  linarith

theorem not_bigO_one_of_linear_lower (D : ℕ → ℝ)
    (hD : ∀ n : ℕ, (n : ℝ) / 2 - 1 < D n) :
    ¬ D =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  intro hO
  obtain ⟨C, _hC, hbound⟩ := hO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound.bound
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (2 * C + 2))
  have hnN : N ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) hn.le)
  have hlarge : 2 * C + 2 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hb := hN n hnN
  simp only [Real.norm_eq_abs, abs_one, mul_one] at hb
  have hle := le_abs_self (D n)
  have hd := hD n
  linarith

theorem every_trajectory_violates_sqrt_log (S : ℕ → ℝ) :
    ¬ (deviation S) =O[atTop] (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) :=
  not_bigO_sqrt_log_of_linear_lower _ (deviation_linear_lower S)

theorem every_maximum_violates_both_bounds {Ω : Type} [Nonempty Ω]
    (S : Ω → ℕ → ℝ) :
    (¬ (maximalDeviation S) =O[atTop] (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)))) ∧
      (¬ (maximalDeviation S) =O[atTop] (fun _ : ℕ => (1 : ℝ))) :=
  ⟨not_bigO_sqrt_log_of_linear_lower _ (maximal_linear_lower S),
   not_bigO_one_of_linear_lower _ (maximal_linear_lower S)⟩

theorem quarter_bound_fails {Ω : Type} [Nonempty Ω] (S : Ω → ℕ → ℝ) :
    (1 : ℝ) / 4 < maximalDeviation S 3 := by
  have h := maximal_linear_lower S 3
  norm_num at h
  linarith

def dyadicWalk (n : ℕ) : ℝ := ((Finset.range n).sum (fun i => 2 ^ (i + 1)) : ℕ)

theorem dyadic_deviation (n : ℕ) : deviation dyadicWalk n = (n : ℝ) / 2 := by
  unfold deviation dyadicWalk
  rw [Int.fract_natCast, zero_sub, abs_neg, abs_of_nonneg (by positivity)]

#print axioms deviation_linear_lower
#print axioms deviation_le_maximal
#print axioms maximal_linear_lower
#print axioms not_bigO_sqrt_log_of_linear_lower
#print axioms not_bigO_one_of_linear_lower
#print axioms every_trajectory_violates_sqrt_log
#print axioms every_maximum_violates_both_bounds
#print axioms quarter_bound_fails
#print axioms dyadic_deviation

end Conjecture7866
