import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace Counterexample

/-- The actual convergent factorial series, including the term of index zero. -/
def L : ℝ := liouvilleNumber 10

theorem series_summable : Summable (fun n : ℕ => 1 / (10 : ℝ) ^ n.factorial) :=
  LiouvilleNumber.summable (by norm_num)

theorem L_liouville : Liouville L :=
  liouville_liouvilleNumber (by norm_num)

/-- Translation preserves every strict rational approximation, with the same denominator. -/
theorem liouville_add_one {x : ℝ} (hx : Liouville x) : Liouville (x + 1) := by
  intro n
  obtain ⟨a, b, hb, hne, herr⟩ := hx n
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans (by norm_num) hb))
  have hfrac : ((a + b : ℤ) : ℝ) / b = (a : ℝ) / b + 1 := by
    push_cast
    field_simp
  refine ⟨a + b, b, hb, ?_, ?_⟩
  · rw [hfrac]
    intro h
    apply hne
    linarith
  · rw [hfrac]
    convert herr using 1 <;> congr 1 <;> ring

theorem translated_liouville : Liouville (L + 1) := liouville_add_one L_liouville

theorem both_transcendental : Transcendental ℤ L ∧ Transcendental ℤ (L + 1) :=
  ⟨L_liouville.transcendental, translated_liouville.transcendental⟩

def pair : Fin 2 → ℝ := ![L, L + 1]
def relation : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1 - MvPolynomial.X 0 - 1

theorem pair_distinct : pair 0 ≠ pair 1 := by
  simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linarith

theorem relation_nonzero : relation ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℚ))) h
  norm_num [relation] at he

theorem relation_vanishes : MvPolynomial.aeval pair relation = 0 := by
  simp [relation, pair]

theorem pair_not_algebraicIndependent : ¬ AlgebraicIndependent ℚ pair := by
  intro h
  exact relation_nonzero (h.eq_zero_of_aeval_eq_zero relation relation_vanishes)

/-- Liouville numbers are the standard U₁ subclass of Mahler U-numbers.
The formal statement uses their full rational approximation characterization. -/
theorem counterexample :
    ∃ x y : ℝ, Liouville x ∧ Liouville y ∧ x ≠ y ∧
      Transcendental ℤ x ∧ Transcendental ℤ y ∧
      ¬ AlgebraicIndependent ℚ ![x, y] := by
  exact ⟨L, L + 1, L_liouville, translated_liouville, pair_distinct,
    both_transcendental.1, both_transcendental.2, pair_not_algebraicIndependent⟩

#print axioms series_summable
#print axioms L_liouville
#print axioms liouville_add_one
#print axioms both_transcendental
#print axioms relation_nonzero
#print axioms relation_vanishes
#print axioms pair_not_algebraicIndependent
#print axioms counterexample
end Counterexample
