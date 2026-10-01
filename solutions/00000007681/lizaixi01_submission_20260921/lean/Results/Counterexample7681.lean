import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Counterexample to TLMC 00000007681 at q = 3/4, n = 2, k = 1.

The recurrence in the conjecture is given the standard continuous q-Hermite
initial values H_0 = 1, H_1 = 2X. These follow from NIST DLMF 18.28.16.
Every ordered-root table below is proved exhaustive and strictly increasing.
Fin indices are zero-based: source index k corresponds to Fin value k - 1.
Only the first conjunct (the stated interlacing inequality) is refuted.
-/

open Polynomial

namespace Counterexample7681

noncomputable def H (q : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C 2 * X
  | n + 2 => C 2 * X * H q (n + 1) - C (1 - q ^ (n + 1)) * H q n

theorem recurrence (q : ℝ) (n : ℕ) :
    C 2 * X * H q (n + 1) = H q (n + 2) + C (1 - q ^ (n + 1)) * H q n := by
  rw [H]
  ring

theorem H_two_eval (x : ℝ) : (H (3 / 4) 2).eval x = 4 * x ^ 2 - 1 / 4 := by
  norm_num [H]
  ring

theorem H_three_eval (x : ℝ) : (H (3 / 4) 3).eval x = x * (8 * x ^ 2 - 11 / 8) := by
  norm_num [H]
  ring

theorem H_two_roots (x : ℝ) :
    (H (3 / 4) 2).eval x = 0 ↔ x = -1 / 4 ∨ x = 1 / 4 := by
  rw [H_two_eval]
  constructor
  · intro h
    have hp : (x + 1 / 4) * (x - 1 / 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hl | hr
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

theorem H_three_roots (x : ℝ) :
    (H (3 / 4) 3).eval x = 0 ↔
      x = -(Real.sqrt 11) / 8 ∨ x = 0 ∨ x = Real.sqrt 11 / 8 := by
  have hs : (Real.sqrt (11 : ℝ)) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  rw [H_three_eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hq
    · exact Or.inr (Or.inl hz)
    · have hp : (x + Real.sqrt 11 / 8) * (x - Real.sqrt 11 / 8) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hp with hl | hr
      · left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl)
    · apply mul_eq_zero.mpr
      right
      nlinarith
    · norm_num
    · apply mul_eq_zero.mpr
      right
      nlinarith

/-- A strictly increasing, exhaustive enumeration of all real roots. -/
def OrderedRoots {n : ℕ} (p : ℝ[X]) (r : Fin n → ℝ) : Prop :=
  StrictMono r ∧ ∀ x : ℝ, p.eval x = 0 ↔ ∃ i : Fin n, r i = x

noncomputable def roots₂ (i : Fin 2) : ℝ := if i = 0 then -1 / 4 else 1 / 4

noncomputable def roots₃ (i : Fin 3) : ℝ :=
  if i = 0 then -(Real.sqrt 11) / 8 else if i = 1 then 0 else Real.sqrt 11 / 8

theorem ordered_roots_two : OrderedRoots (H (3 / 4) 2) roots₂ := by
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [roots₂] at *
  · intro x
    rw [H_two_roots]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num [roots₂]⟩
      · exact ⟨1, by norm_num [roots₂]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp [roots₂] at hi <;> simp [← hi]

theorem ordered_roots_three : OrderedRoots (H (3 / 4) 3) roots₃ := by
  have hs : 0 < Real.sqrt (11 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  constructor
  · intro a b hab
    change a.val < b.val at hab
    fin_cases a <;> fin_cases b <;> norm_num at hab <;>
      norm_num [roots₃] <;> linarith
  · intro x
    rw [H_three_roots]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp [roots₃]⟩
      · exact ⟨1, by simp [roots₃]⟩
      · exact ⟨2, by simp [roots₃]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp [roots₃] at hi <;> simp [← hi]

/-- The source's first conjunct, restricted only to indices for which both
    right-hand roots exist. A Fin index k represents the source index k+1;
    consequently source indices 2k and 2k+1 become 2*k.val+1 and 2*k.val+2. -/
def ConjecturedInterlacing : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    ∀ (n : ℕ) (r : Fin n → ℝ) (s : Fin (n + 1) → ℝ),
      OrderedRoots (H q n) r → OrderedRoots (H q (n + 1)) s →
      ∀ (k : Fin n) (hk : 2 * k.val + 2 < n + 1),
        s ⟨2 * k.val + 1, by omega⟩ < r k ∧
        r k < s ⟨2 * k.val + 2, hk⟩

theorem valid_parameter : (0 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by norm_num

theorem counterexample_indices :
    ¬ (roots₃ 1 < roots₂ 0 ∧ roots₂ 0 < roots₃ 2) := by
  norm_num [roots₃, roots₂]

theorem conjectured_interlacing_false : ¬ ConjecturedInterlacing := by
  intro h
  have hi := h (3 / 4) valid_parameter.1 valid_parameter.2 2 roots₂ roots₃
    ordered_roots_two ordered_roots_three (0 : Fin 2) (by norm_num)
  exact counterexample_indices hi

/-- Whatever precise meaning is assigned to the source's later monotonicity
    clause, its conjunction with the stated interlacing assertion is false. -/
theorem full_conjecture_false (monotonicityClause : Prop) :
    ¬ (ConjecturedInterlacing ∧ monotonicityClause) := by
  exact fun h => conjectured_interlacing_false h.1

#print axioms recurrence
#print axioms H_two_eval
#print axioms H_three_eval
#print axioms H_two_roots
#print axioms H_three_roots
#print axioms ordered_roots_two
#print axioms ordered_roots_three
#print axioms counterexample_indices
#print axioms conjectured_interlacing_false
#print axioms full_conjecture_false

end Counterexample7681
