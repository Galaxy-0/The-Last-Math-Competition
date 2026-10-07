/-
Problem 00000008482 (verbatim):
"Definition: The convergence error of Kingman's subadditive ergodic theorem: the decay order of |n^{-1}E[X_n] - gamma| in n. Conjecture: The universal upper bound for bounded subadditive families is O(log n/n) (a logarithmic harmonic law); the bound cannot be improved, extremal examples being realized by discretization deviations of Sturmian balanced words (a Sturmian extremal law); and in the unbounded case the error can decay arbitrarily slowly (an arbitrary slowness law). (Kingman Sturmian extremal logarithmic decay)"

Reading: bounded means bounded one-step costs, linear interval growth, or
bounded successive increments. We refute the upper-bound clause even with all
three restrictions. A single deterministic stationary family suffices.
Uniform boundedness by one constant over ALL interval lengths is a different
reading: the square-root family does not satisfy it; see the report.
-/
import Mathlib

/-! # Disproof of TLMC 00000008482
The opening module documentation gives the conjecture verbatim and the reading.
It uses a block comment before the import because Lean requires imports before
module documentation commands. All definitions and proofs are in this file.
-/

open Filter Asymptotics
open scoped Topology

namespace KingmanCounterexample

abbrev Family := ℕ → ℕ → ℝ

/-- The restrictions include nonnegativity and normalized linear growth. -/
structure BoundedStationarySubadditive (X : Family) : Prop where
  subadditive : ∀ l m n, l ≤ m → m ≤ n → X l n ≤ X l m + X m n
  stationary : ∀ m n k, X (m + k) (n + k) = X m n
  bounds : ∀ m n, m ≤ n → 0 ≤ X m n ∧ X m n ≤ (n - m : ℕ)
  one_step : ∀ m, X m (m + 1) = 1
  increments : ∀ m n, m ≤ n → |X m (n + 1) - X m n| ≤ 1

noncomputable def sqrtFamily (m n : ℕ) : ℝ := Real.sqrt (n - m : ℕ)

noncomputable def gamma (X : Family) : ℝ :=
  limUnder atTop (fun n : ℕ => X 0 n / (n : ℝ))

lemma sqrt_subadditive (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsa := Real.sq_sqrt ha
    have hsb := Real.sq_sqrt hb
    have hp : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
    nlinarith

lemma sqrt_nat_le (n : ℕ) : Real.sqrt (n : ℝ) ≤ n := by
  apply Real.sqrt_le_self_iff.mpr
  rcases Nat.eq_zero_or_pos n with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem sqrtFamily_hypotheses : BoundedStationarySubadditive sqrtFamily := by
  constructor
  · intro l m n hlm hmn
    have he : n - l = (m - l) + (n - m) := by omega
    simpa only [sqrtFamily, he, Nat.cast_add] using
      sqrt_subadditive ((m - l : ℕ) : ℝ) ((n - m : ℕ) : ℝ)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro m n k
    have he : n + k - (m + k) = n - m := by omega
    simp only [sqrtFamily, he]
  · intro m n _
    exact ⟨Real.sqrt_nonneg _, sqrt_nat_le _⟩
  · intro m
    simp [sqrtFamily]
  · intro m n hmn
    have he : n + 1 - m = (n - m) + 1 := by omega
    have hmono : sqrtFamily m n ≤ sqrtFamily m (n + 1) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show n - m ≤ n + 1 - m by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hs := sqrt_subadditive ((n - m : ℕ) : ℝ) 1 (Nat.cast_nonneg _) (by norm_num)
    simp only [Real.sqrt_one] at hs
    dsimp [sqrtFamily]
    rw [he, Nat.cast_add, Nat.cast_one]
    linarith

theorem sqrtFamily_error (n : ℕ) :
    |sqrtFamily 0 n / (n : ℝ) - 0| = (Real.sqrt (n : ℝ))⁻¹ := by
  simp only [sqrtFamily, Nat.sub_zero, sub_zero]
  rw [abs_of_nonneg (by positivity), Real.sqrt_div_self]

theorem sqrtFamily_limit :
    Tendsto (fun n : ℕ => sqrtFamily 0 n / (n : ℝ)) atTop (𝓝 0) := by
  simp only [sqrtFamily, Nat.sub_zero, Real.sqrt_div_self]
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem sqrtFamily_gamma : gamma sqrtFamily = 0 := sqrtFamily_limit.limUnder_eq

/-- The infimum is over positive lengths, parametrized by n+1. -/
theorem sqrtFamily_infimum :
    sInf (Set.range (fun n : ℕ => sqrtFamily 0 (n + 1) / ((n + 1 : ℕ) : ℝ))) = 0 := by
  let f : ℕ → ℝ := fun n => sqrtFamily 0 (n + 1) / ((n + 1 : ℕ) : ℝ)
  have hf : ∀ n, 0 ≤ f n := by intro n; dsimp [f, sqrtFamily]; positivity
  have hb : BddBelow (Set.range f) := ⟨0, by rintro x ⟨n, rfl⟩; exact hf n⟩
  apply le_antisymm
  · have ht : Tendsto f atTop (𝓝 0) :=
      sqrtFamily_limit.comp (tendsto_add_atTop_nat 1)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n => csInf_le hb ⟨n, rfl⟩)
  · exact le_csInf (Set.range_nonempty f) (by rintro x ⟨n, rfl⟩; exact hf n)

lemma log_littleO_sqrt :
    (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n => Real.sqrt (n : ℝ)) := by
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem sqrtFamily_not_bigO :
    ¬ ((fun n : ℕ => |sqrtFamily 0 n / (n : ℝ) - 0|)
      =O[atTop] (fun n => Real.log (n : ℝ) / (n : ℝ))) := by
  intro h
  have hm := h.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  have hs : (fun n : ℕ => Real.sqrt (n : ℝ)) =O[atTop]
      (fun n => Real.log (n : ℝ)) := by
    apply hm.congr'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      simp only [sub_zero, sqrtFamily, Nat.sub_zero,
        abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))]
      exact div_mul_cancel₀ _ hn0
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      exact div_mul_cancel₀ _ hn0
  have hne : ∃ᶠ n : ℕ in atTop, Real.sqrt (n : ℝ) ≠ 0 := by
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))
  exact hs.not_isLittleO hne log_littleO_sqrt

/-- The per-family O reading, with the actual limiting constant. -/
def UniversalUpperBound : Prop :=
  ∀ X : Family, BoundedStationarySubadditive X →
    Tendsto (fun n : ℕ => X 0 n / (n : ℝ)) atTop (𝓝 (gamma X)) →
    (fun n : ℕ => |X 0 n / (n : ℝ) - gamma X|)
      =O[atTop] (fun n => Real.log (n : ℝ) / (n : ℝ))

theorem conjecture_00000008482_false : ¬ UniversalUpperBound := by
  intro h
  have ht : Tendsto (fun n : ℕ => sqrtFamily 0 n / (n : ℝ)) atTop
      (𝓝 (gamma sqrtFamily)) := by rw [sqrtFamily_gamma]; exact sqrtFamily_limit
  have ho := h sqrtFamily sqrtFamily_hypotheses ht
  rw [sqrtFamily_gamma] at ho
  exact sqrtFamily_not_bigO ho

/-- One constant bounds every interval value, independently of both endpoints. -/
def UniformlyBounded (X : Family) : Prop :=
  ∃ C : ℝ, ∀ m n, |X m n| ≤ C

/-- Uniform boundedness alone forces the normalized limit and `gamma` to be zero. -/
theorem uniformlyBounded_limit {X : Family} (hX : UniformlyBounded X) :
    Tendsto (fun n : ℕ => X 0 n / (n : ℝ)) atTop (𝓝 0) ∧ gamma X = 0 := by
  obtain ⟨C, hC⟩ := hX
  have ht : Tendsto (fun n : ℕ => X 0 n / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => C / (n : ℝ))
    · intro n
      rw [Real.norm_eq_abs, abs_div,
        abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
      exact div_le_div_of_nonneg_right (hC 0 n) (Nat.cast_nonneg n)
    · exact tendsto_const_div_atTop_nhds_zero_nat C
  exact ⟨ht, ht.limUnder_eq⟩

/-- Every uniformly bounded family's error is strictly smaller than the logarithmic scale. -/
theorem uniformlyBounded_error_isLittleO {X : Family} (hX : UniformlyBounded X) :
    (fun n : ℕ => |X 0 n / (n : ℝ) - gamma X|)
      =o[atTop] (fun n => Real.log (n : ℝ) / (n : ℝ)) := by
  have hg := (uniformlyBounded_limit hX).2
  obtain ⟨C, hC⟩ := hX
  have hb : (fun n : ℕ => X 0 n) =O[atTop] (fun _ => (1 : ℝ)) := by
    apply isBigO_of_le' (c := C)
    intro n
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using hC 0 n
  have hl : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      (fun n => Real.log (n : ℝ)) := by
    apply (isLittleO_one_left_iff ℝ).mpr
    exact tendsto_norm_atTop_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hd := (hb.trans_isLittleO hl).mul_isBigO
    (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop)
  rw [hg]
  simpa only [sub_zero, div_eq_mul_inv] using hd.abs_left

/-- Exactly stationarity, ordered subadditivity, and a bound over all intervals. -/
structure UniformlyBoundedStationarySubadditive (X : Family) : Prop where
  stationary : ∀ m n k, X (m + k) (n + k) = X m n
  subadditive : ∀ l m n, l ≤ m → m ≤ n → X l n ≤ X l m + X m n
  uniformly_bounded : UniformlyBounded X

/-- Logarithmic sharpness would require an admissible error that is not little-o. -/
def SharpnessClauseUniform : Prop :=
  ∃ X : Family, UniformlyBoundedStationarySubadditive X ∧
    ¬ ((fun n : ℕ => |X 0 n / (n : ℝ) - gamma X|)
      =o[atTop] (fun n => Real.log (n : ℝ) / (n : ℝ)))

theorem sharpness_false_uniform : ¬ SharpnessClauseUniform := by
  rintro ⟨X, hX, hn⟩
  exact hn (uniformlyBounded_error_isLittleO hX.uniformly_bounded)

/-- Under the linear-growth / bounded-increment reading the first clause fails
(the square-root family); under the uniformly-bounded reading the second clause
fails. Either way the conjectured conjunction is false. -/
theorem conjecture_00000008482_false_both_readings :
    ¬ UniversalUpperBound ∧ ¬ SharpnessClauseUniform :=
  ⟨conjecture_00000008482_false, sharpness_false_uniform⟩

end KingmanCounterexample

#print axioms KingmanCounterexample.sqrtFamily_hypotheses
#print axioms KingmanCounterexample.sqrtFamily_limit
#print axioms KingmanCounterexample.sqrtFamily_infimum
#print axioms KingmanCounterexample.sqrtFamily_not_bigO
#print axioms KingmanCounterexample.conjecture_00000008482_false
#print axioms KingmanCounterexample.uniformlyBounded_limit
#print axioms KingmanCounterexample.uniformlyBounded_error_isLittleO
#print axioms KingmanCounterexample.sharpness_false_uniform
#print axioms KingmanCounterexample.conjecture_00000008482_false_both_readings
