import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace Conjecture2831

/-- A stochastic HMM with one hidden state and two observable symbols. -/
structure HMM where
  initial : Fin 1 → ℝ
  transition : Fin 1 → Fin 1 → ℝ
  emission : Fin 1 → Fin 2 → ℝ
  initial_nonneg : ∀ i, 0 ≤ initial i
  initial_sum : (∑ i, initial i) = 1
  transition_nonneg : ∀ i j, 0 ≤ transition i j
  transition_sum : ∀ i, (∑ j, transition i j) = 1
  emission_nonneg : ∀ i j, 0 ≤ emission i j
  emission_sum : ∀ i, (∑ j, emission i j) = 1

def observed (p : HMM) : Fin 2 → ℝ := fun j => ∑ i, p.initial i * p.emission i j
def modelImage : Set (Fin 2 → ℝ) := Set.range observed
def line (t : ℝ) : Fin 2 → ℝ := ![t, 1 - t]

def bernoulliHMM (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HMM where
  initial := fun _ => 1
  transition := fun _ _ => 1
  emission := fun _ => line t
  initial_nonneg := by intro i; norm_num
  initial_sum := by simp
  transition_nonneg := by intro i j; norm_num
  transition_sum := by intro i; simp
  emission_nonneg := by
    intro i j
    fin_cases j <;> simp [line] <;> linarith [ht.1, ht.2]
  emission_sum := by intro i; simp [line, Fin.sum_univ_two]

theorem bernoulli_observed (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    observed (bernoulliHMM t ht) = line t := by
  funext j
  simp [observed, bernoulliHMM]

theorem interval_in_image {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : line t ∈ modelImage :=
  ⟨bernoulliHMM t ht, bernoulli_observed t ht⟩

theorem observed_nonnegative (p : HMM) (j : Fin 2) : 0 ≤ observed p j := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (p.initial_nonneg i) (p.emission_nonneg i j))

theorem outside_point : line 2 ∉ modelImage := by
  rintro ⟨p, hp⟩
  have hn := observed_nonnegative p 1
  rw [hp] at hn
  norm_num [line] at hn

abbrev Poly := MvPolynomial (Fin 2) ℝ
def pullback (p : Poly) : Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, 1 - Polynomial.X] p

theorem eval_pullback (p : Poly) (t : ℝ) :
    Polynomial.aeval t (pullback p) = MvPolynomial.aeval (line t) p := by
  rw [pullback, MvPolynomial.comp_aeval_apply]
  have he : (fun i : Fin 2 => Polynomial.aeval t
      ((![Polynomial.X, 1 - Polynomial.X] : Fin 2 → Polynomial ℝ) i)) = line t := by
    funext i
    fin_cases i <;> simp [line]
  rw [he]

theorem vanish_on_interval_then_line (p : Poly)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, MvPolynomial.aeval (line t) p = 0) :
    ∀ t : ℝ, MvPolynomial.aeval (line t) p = 0 := by
  have hz : pullback p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).mono
    intro t ht
    change Polynomial.eval t (pullback p) = 0
    rw [← Polynomial.coe_aeval_eq_eval, eval_pullback]
    exact hp t ht
  intro t
  rw [← eval_pullback, hz, map_zero]

/-- The common zero locus of any family of real polynomials. -/
def IsRealAlgebraic (S : Set (Fin 2 → ℝ)) : Prop :=
  ∃ equations : Set Poly, ∀ x, x ∈ S ↔ ∀ p ∈ equations, MvPolynomial.aeval x p = 0

theorem conjecture_false : ¬ IsRealAlgebraic modelImage := by
  rintro ⟨equations, heq⟩
  apply outside_point
  apply (heq (line 2)).2
  intro p hp
  apply vanish_on_interval_then_line p
  intro t ht
  exact (heq (line t)).1 (interval_in_image ht) p hp

#print axioms bernoulli_observed
#print axioms observed_nonnegative
#print axioms outside_point
#print axioms eval_pullback
#print axioms vanish_on_interval_then_line
#print axioms conjecture_false
end Conjecture2831
