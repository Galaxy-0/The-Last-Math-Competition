/-
# TLMC problem 00000000399: Calkin-Wilf digit golden law

Conjecture (verbatim): "Definition: The maximal number of digits of denominators
at level n of the Calkin–Wilf tree. Conjecture: The maximum equals n·log₂φ +
O(log n); and the constant log₂φ comes from the branching geometry of the tree.
(Calkin-Wilf digit golden law)"

Reading: digits are binary digits, the root (1,1) has level zero, and the two
children of (a,b) are (a,a+b) and (a+b,b). The explanatory geometry clause is
realized by the sharp Fibonacci invariant and the consecutive-Fibonacci
witnesses. We prove an explicit O(1) bound, hence the stated O(log n) bound.
All generated pairs are positive and coprime, so their second coordinates
are the denominators of the fractions in lowest terms. We also prove the
base-b law for every integer b ≥ 2, and show that the printed binary
coefficient gives unbounded error, not O(log n), for every b ≥ 3.
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# TLMC problem 00000000399: Calkin-Wilf digit golden law

Conjecture (verbatim): "Definition: The maximal number of digits of denominators
at level n of the Calkin–Wilf tree. Conjecture: The maximum equals n·log₂φ +
O(log n); and the constant log₂φ comes from the branching geometry of the tree.
(Calkin-Wilf digit golden law)"

Reading: digits are binary digits, the root (1,1) has level zero, and the two
children of (a,b) are (a,a+b) and (a+b,b). The explanatory geometry clause is
realized by the sharp Fibonacci invariant and the consecutive-Fibonacci
witnesses. We prove an explicit O(1) bound, hence the stated O(log n) bound.
All generated pairs are positive and coprime, so their second coordinates
are the denominators of the fractions in lowest terms. We also prove the
base-b law for every integer b ≥ 2, and show that the printed binary
coefficient gives unbounded error, not O(log n), for every b ≥ 3.
-/

namespace CalkinWilf399
open Filter Asymptotics
open scoped Topology

def left (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.1 + p.2)
def right (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + p.2, p.2)

def level : ℕ → Finset (ℕ × ℕ)
  | 0 => {(1, 1)}
  | n + 1 => (level n).image left ∪ (level n).image right

def maxDen (n : ℕ) : ℕ := (level n).sup Prod.snd
def digits2 (m : ℕ) : ℕ := (Nat.digits 2 m).length
def maxDigits (n : ℕ) : ℕ := (level n).sup (fun p => digits2 p.2)

/-- Digit lengths and their actual level maximum in an arbitrary integer base. -/
def digitsBase (b m : ℕ) : ℕ := (Nat.digits b m).length
def maxDigitsBase (b n : ℕ) : ℕ := (level n).sup (fun p => digitsBase b p.2)

lemma left_mem {n : ℕ} {p : ℕ × ℕ} (h : p ∈ level n) : left p ∈ level (n+1) := by
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
lemma right_mem {n : ℕ} {p : ℕ × ℕ} (h : p ∈ level n) : right p ∈ level (n+1) := by
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

/-- The labels really are positive reduced fractions. -/
theorem level_wellformed (n : ℕ) : ∀ p ∈ level n,
    0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 := by
  induction n with
  | zero => simp [level]
  | succ n ih =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb, hc⟩ := ih q hq
      exact ⟨ha, by dsimp [left]; omega, Nat.coprime_self_add_right.mpr hc⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb, hc⟩ := ih q hq
      exact ⟨by dsimp [right]; omega, hb, Nat.coprime_add_self_left.mpr hc⟩

/-- The sum bound is the extra information that makes the induction sharp. -/
theorem level_bounds (n : ℕ) : ∀ p ∈ level n,
    p.1 ≤ Nat.fib (n+2) ∧ p.2 ≤ Nat.fib (n+2) ∧
      p.1 + p.2 ≤ Nat.fib (n+3) := by
  induction n with
  | zero => simp [level]; norm_num
  | succ n ih =>
    intro p hp
    have hmono : Nat.fib (n+2) ≤ Nat.fib (n+3) := Nat.fib_mono (by omega)
    have hrec : Nat.fib (n+4) = Nat.fib (n+2) + Nat.fib (n+3) := by
      simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n+2))
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb, hs⟩ := ih q hq
      dsimp [left]
      simpa only [Nat.add_assoc] using
        (show q.1 ≤ Nat.fib (n+3) ∧ q.1+q.2 ≤ Nat.fib (n+3) ∧
          q.1+(q.1+q.2) ≤ Nat.fib (n+4) from ⟨ha.trans hmono, hs, by omega⟩)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb, hs⟩ := ih q hq
      dsimp [right]
      simpa only [Nat.add_assoc] using
        (show q.1+q.2 ≤ Nat.fib (n+3) ∧ q.2 ≤ Nat.fib (n+3) ∧
          (q.1+q.2)+q.2 ≤ Nat.fib (n+4) from ⟨hs, hb.trans hmono, by omega⟩)

/-- Mirror zigzag branches attain consecutive Fibonacci labels. -/
theorem fibonacci_witnesses (n : ℕ) :
    (Nat.fib (n+1), Nat.fib (n+2)) ∈ level n ∧
    (Nat.fib (n+2), Nat.fib (n+1)) ∈ level n := by
  induction n with
  | zero => norm_num [level]
  | succ n ih =>
    have hrec : Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) := by
      simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n+1))
    constructor
    · convert left_mem ih.2 using 1
      simp [left, hrec, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · convert right_mem ih.1 using 1
      simp [right, hrec, Nat.add_assoc]

/-- Exact maximum over the actual recursively generated level. -/
theorem maxDen_eq_fib (n : ℕ) : maxDen n = Nat.fib (n+2) := by
  apply le_antisymm
  · exact Finset.sup_le (fun p hp => (level_bounds n p hp).2.1)
  · exact Finset.le_sup (f := Prod.snd) (fibonacci_witnesses n).1

/-- Monotonicity of digit count transfers the attained denominator maximum. -/
theorem maxDigits_eq_fib_digits (n : ℕ) :
    maxDigits n = digits2 (Nat.fib (n+2)) := by
  apply le_antisymm
  · exact Finset.sup_le (fun p hp =>
      Nat.le_length_digits_le 2 _ _ (level_bounds n p hp).2.1)
  · exact Finset.le_sup (f := fun p => digits2 p.2) (fibonacci_witnesses n).1

/-- Binary digit-list length agrees with Mathlib's binary size. -/
theorem digits2_eq_size (m : ℕ) : digits2 m = Nat.size m := by
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num : 1 < 2) m).mpr
      (Nat.lt_size_self m)
  · exact Nat.size_le.mpr
      ((Nat.digits_length_le_iff (by norm_num : 1 < 2) m).mp (le_refl _))

theorem maxDigits_eq_size (n : ℕ) : maxDigits n = Nat.size (Nat.fib (n+2)) := by
  rw [maxDigits_eq_fib_digits, digits2_eq_size]

/-- Exact integer logarithm formula for the positive maximum denominator. -/
theorem maxDigits_eq_log (n : ℕ) : maxDigits n = Nat.log 2 (Nat.fib (n+2)) + 1 := by
  rw [maxDigits_eq_fib_digits, digits2]
  exact Nat.length_digits 2 _ (by norm_num) (by
    have := Nat.fib_pos.mpr (show 0 < n+2 by omega)
    omega)

/-- Growth bounds from the same two-term recurrence; no asymptotic formula is needed. -/
theorem fib_golden_bounds (n : ℕ) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n+2) : ℝ) ∧
    (Nat.fib (n+2) : ℝ) ≤ Real.goldenRatio ^ (n+1) := by
  have hphi := Real.one_lt_goldenRatio
  have hphi2 := Real.goldenRatio_sq
  have hphi_lt_two := Real.goldenRatio_lt_two
  induction n using Nat.twoStepInduction with
  | zero => norm_num; exact hphi.le
  | one => norm_num; constructor <;> nlinarith
  | more n ih0 ih1 =>
    have hrec : (Nat.fib (n+2+2) : ℝ) =
        (Nat.fib (n+2) : ℝ) + (Nat.fib (n+1+2) : ℝ) := by
      exact_mod_cast (Nat.fib_add_two (n := n+2))
    have hp0 : Real.goldenRatio ^ (n+2) =
        Real.goldenRatio ^ n + Real.goldenRatio ^ (n+1) := by
      rw [pow_add, hphi2, pow_succ]; ring
    have hp1 : Real.goldenRatio ^ (n+2+1) =
        Real.goldenRatio ^ (n+1) + Real.goldenRatio ^ (n+1+1) := by
      rw [show n+2+1 = (n+1)+2 by omega, pow_add, hphi2, pow_succ]; ring
    constructor
    · rw [hrec, hp0]; exact add_le_add ih0.1 ih1.1
    · rw [hrec, hp1]; exact add_le_add ih0.2 ih1.2

lemma digits2_log_bounds {m : ℕ} (hm : 0 < m) :
    Real.logb 2 (m : ℝ) < (digits2 m : ℝ) ∧
    (digits2 m : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have hlog : 0 ≤ Real.logb 2 (m : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have hd : (digits2 m : ℝ) = (⌊Real.logb 2 (m : ℝ)⌋₊ : ℝ) + 1 := by
    rw [digits2, Nat.length_digits 2 m (by norm_num) (by omega), Nat.cast_add,
      Nat.cast_one]
    have hf : ⌊Real.logb 2 (m : ℝ)⌋₊ = Nat.log 2 m := by
      simpa using Real.natFloor_logb_natCast 2 m
    rw [hf]
  rw [hd]
  exact ⟨Nat.lt_floor_add_one _, by linarith [Nat.floor_le hlog]⟩

/-- A uniform, explicit bound, valid even at level zero. -/
theorem bounded_error (n : ℕ) :
    |(maxDigits n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio| ≤
      Real.logb 2 Real.goldenRatio + 1 := by
  have hp : 0 < Nat.fib (n+2) := Nat.fib_pos.mpr (by omega)
  have hb := fib_golden_bounds n
  have hd := digits2_log_bounds hp
  have hlo := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (pow_pos Real.goldenRatio_pos n) hb.1
  have hhi := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (show (0 : ℝ) < Nat.fib (n+2) by exact_mod_cast hp) hb.2
  rw [Real.logb_pow] at hlo hhi
  rw [maxDigits_eq_fib_digits]
  have hnonneg : 0 ≤ Real.logb 2 Real.goldenRatio :=
    Real.logb_nonneg (by norm_num) Real.one_lt_goldenRatio.le
  simp only [Nat.cast_add, Nat.cast_one] at hhi
  rw [abs_le]
  constructor <;> nlinarith

/-- The existential O(1) form. -/
theorem exists_bounded_error : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |(maxDigits n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio| ≤ C := by
  exact ⟨Real.logb 2 Real.goldenRatio + 1, fun n _ => bounded_error n⟩

/-- The literal error O(log n), at infinity on natural-number levels. -/
theorem digit_error_isBigO_log :
    (fun n : ℕ => (maxDigits n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio)
      =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (tendsto_atTop.1 ht) 1
  apply IsBigO.of_bound (Real.logb 2 Real.goldenRatio + 1)
  filter_upwards [he] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ))]
  have hc : 0 ≤ Real.logb 2 Real.goldenRatio + 1 := by
    have := Real.logb_nonneg (b := 2) (by norm_num) Real.one_lt_goldenRatio.le
    linarith
  exact (bounded_error n).trans (le_mul_of_one_le_right hc hn)

/-- Full package: sharp maximum, exact binary digits, stronger bound, and the conjecture. -/
theorem calkin_wilf_digit_golden_law :
    (∀ n, maxDen n = Nat.fib (n+2)) ∧
    (∀ n, maxDigits n = digits2 (Nat.fib (n+2))) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(maxDigits n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio| ≤ C) ∧
    ((fun n : ℕ => (maxDigits n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio)
      =O[atTop] (fun n : ℕ => Real.log (n : ℝ))) := by
  exact ⟨maxDen_eq_fib, maxDigits_eq_fib_digits, exists_bounded_error,
    digit_error_isBigO_log⟩

/-- The attained maximum transfers to any digit base. -/
theorem maxDigitsBase_eq_fib_digits (b n : ℕ) :
    maxDigitsBase b n = digitsBase b (Nat.fib (n+2)) := by
  apply le_antisymm
  · exact Finset.sup_le (fun p hp =>
      Nat.le_length_digits_le b _ _ (level_bounds n p hp).2.1)
  · exact Finset.le_sup (f := fun p => digitsBase b p.2) (fibonacci_witnesses n).1

/-- Exact integer logarithm formula in every base at least two. -/
theorem maxDigitsBase_eq_log (b n : ℕ) (hb : 2 ≤ b) :
    maxDigitsBase b n = Nat.log b (Nat.fib (n+2)) + 1 := by
  rw [maxDigitsBase_eq_fib_digits, digitsBase]
  exact Nat.length_digits b _ (by omega) (by
    have := Nat.fib_pos.mpr (show 0 < n+2 by omega)
    omega)

lemma digitsBase_log_bounds {b m : ℕ} (hb : 2 ≤ b) (hm : 0 < m) :
    Real.logb b (m : ℝ) < (digitsBase b m : ℝ) ∧
    (digitsBase b m : ℝ) ≤ Real.logb b (m : ℝ) + 1 := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hlog : 0 ≤ Real.logb b (m : ℝ) :=
    Real.logb_nonneg hb' (by exact_mod_cast hm)
  have hd : (digitsBase b m : ℝ) = (⌊Real.logb b (m : ℝ)⌋₊ : ℝ) + 1 := by
    rw [digitsBase, Nat.length_digits b m (by omega) (by omega), Nat.cast_add,
      Nat.cast_one]
    have hf : ⌊Real.logb b (m : ℝ)⌋₊ = Nat.log b m := by
      simpa using Real.natFloor_logb_natCast b m
    rw [hf]
  rw [hd]
  exact ⟨Nat.lt_floor_add_one _, by linarith [Nat.floor_le hlog]⟩

/-- A stronger one-sided version of the all-base O(1) law. -/
theorem base_digit_error_bounds (b n : ℕ) (hb : 2 ≤ b) :
    0 < (maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb b Real.goldenRatio ∧
    (maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb b Real.goldenRatio ≤
      Real.logb b Real.goldenRatio + 1 := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hp : 0 < Nat.fib (n+2) := Nat.fib_pos.mpr (by omega)
  have hf := fib_golden_bounds n
  have hd := digitsBase_log_bounds hb hp
  have hlo := Real.logb_le_logb_of_le hb'
    (pow_pos Real.goldenRatio_pos n) hf.1
  have hhi := Real.logb_le_logb_of_le hb'
    (show (0 : ℝ) < Nat.fib (n+2) by exact_mod_cast hp) hf.2
  rw [Real.logb_pow] at hlo hhi
  rw [maxDigitsBase_eq_fib_digits]
  simp only [Nat.cast_add, Nat.cast_one] at hhi
  constructor <;> linarith

/-- Explicit uniform error bound in every base b ≥ 2, including level zero. -/
theorem base_bounded_error (b n : ℕ) (hb : 2 ≤ b) :
    |(maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb b Real.goldenRatio| ≤
      Real.logb b Real.goldenRatio + 1 := by
  rw [abs_of_pos (base_digit_error_bounds b n hb).1]
  exact (base_digit_error_bounds b n hb).2

/-- Base two specializes to the original maximum. -/
theorem maxDigitsBase_two (n : ℕ) : maxDigitsBase 2 n = maxDigits n := rfl

/-- The slope strictly decreases when the integer base exceeds two. -/
theorem base_slope_lt_binary (b : ℕ) (hb : 3 ≤ b) :
    Real.logb b Real.goldenRatio < Real.logb 2 Real.goldenRatio := by
  have hb' : (2 : ℝ) < b := by exact_mod_cast (show 2 < b by omega)
  unfold Real.logb
  exact div_lt_div_of_pos_left (Real.log_pos Real.one_lt_goldenRatio)
    (Real.log_pos (by norm_num)) (Real.log_lt_log (by norm_num) hb')

/-- The error against the printed binary coefficient has a linear lower bound. -/
theorem binary_coefficient_error_lower (b n : ℕ) (hb : 3 ≤ b) :
    (n : ℝ) * (Real.logb 2 Real.goldenRatio - Real.logb b Real.goldenRatio) -
        (Real.logb b Real.goldenRatio + 1) ≤
      |(maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio| := by
  have h := (base_digit_error_bounds b n (by omega)).2
  have ha := neg_le_abs ((maxDigitsBase b n : ℝ) -
    (n : ℝ) * Real.logb 2 Real.goldenRatio)
  nlinarith

/-- In any base b ≥ 3, the error against the binary coefficient is unbounded. -/
theorem binary_coefficient_error_unbounded (b : ℕ) (hb : 3 ≤ b) :
    ∀ C : ℝ, ∃ n : ℕ,
      C < |(maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio| := by
  intro C
  have hdelta : 0 < Real.logb 2 Real.goldenRatio - Real.logb b Real.goldenRatio :=
    sub_pos.mpr (base_slope_lt_binary b hb)
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((C + (Real.logb b Real.goldenRatio + 1)) /
      (Real.logb 2 Real.goldenRatio - Real.logb b Real.goldenRatio))
  have hn' := (div_lt_iff₀ hdelta).mp hn
  exact ⟨n, by linarith [binary_coefficient_error_lower b n hb]⟩

/-- The linear discrepancy cannot even be O(log n), for any base b ≥ 3. -/
theorem binary_coefficient_error_not_isBigO_log (b : ℕ) (hb : 3 ≤ b) :
    ¬ ((fun n : ℕ => (maxDigitsBase b n : ℝ) -
        (n : ℝ) * Real.logb 2 Real.goldenRatio)
      =O[atTop] (fun n : ℕ => Real.log (n : ℝ))) := by
  intro h
  let δ := Real.logb 2 Real.goldenRatio - Real.logb b Real.goldenRatio
  have hδ : 0 < δ := sub_pos.mpr (base_slope_lt_binary b hb)
  have hl : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have he := (h.trans_isLittleO hl).def (half_pos hδ)
  have hn : ∀ᶠ n : ℕ in atTop,
      2 * (Real.logb b Real.goldenRatio + 1) / δ < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop _)
  obtain ⟨n, he, hn⟩ := (he.and hn).exists
  simp only [Real.norm_eq_abs, Nat.abs_cast] at he
  have hn' := (div_lt_iff₀ hδ).mp hn
  have hlo := binary_coefficient_error_lower b n hb
  change (n : ℝ) * δ - (Real.logb b Real.goldenRatio + 1) ≤ _ at hlo
  nlinarith

/-- Among integer bases at least two, the printed O(log n) claim holds exactly in base two. -/
theorem binary_coefficient_valid_iff (b : ℕ) (hb : 2 ≤ b) :
    ((fun n : ℕ => (maxDigitsBase b n : ℝ) - (n : ℝ) * Real.logb 2 Real.goldenRatio)
      =O[atTop] (fun n : ℕ => Real.log (n : ℝ))) ↔ b = 2 := by
  constructor
  · intro h
    by_contra hne
    exact binary_coefficient_error_not_isBigO_log b (by omega) h
  · rintro rfl
    simpa only [maxDigitsBase_two] using digit_error_isBigO_log

#print axioms level_wellformed
#print axioms fibonacci_witnesses
#print axioms maxDigits_eq_size
#print axioms maxDigits_eq_log
#print axioms bounded_error
#print axioms calkin_wilf_digit_golden_law
#print axioms maxDigitsBase_eq_log
#print axioms base_bounded_error
#print axioms binary_coefficient_error_unbounded
#print axioms binary_coefficient_error_not_isBigO_log
#print axioms binary_coefficient_valid_iff
end CalkinWilf399
