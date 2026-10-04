import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

noncomputable section
namespace ParabolicMultiplierCounterexample
open Polynomial

def quadratic (c : ℂ) : ℂ[X] := X ^ 2 + C c

def iteratePoly (c : ℂ) : ℕ → ℂ[X]
  | 0 => X
  | n + 1 => (quadratic c).comp (iteratePoly c n)

theorem iterate_eval (c z : ℂ) (n : ℕ) :
    (iteratePoly c n).eval z = ((fun w : ℂ => w ^ 2 + c)^[n]) z := by
  induction n with
  | zero => simp [iteratePoly]
  | succ n ih =>
    simp only [iteratePoly, eval_comp, quadratic, eval_add, eval_pow, eval_X, eval_C, ih]
    exact (Function.iterate_succ_apply' (fun w : ℂ => w ^ 2 + c) n z).symm

/-- The actual complex derivative of the actual composed quadratic map. -/
def multiplier (c z : ℂ) (n : ℕ) : ℂ := deriv (fun w => (iteratePoly c n).eval w) z

theorem multiplier_polynomial (c z : ℂ) (n : ℕ) :
    multiplier c z n = (iteratePoly c n).derivative.eval z :=
  (iteratePoly c n).deriv

def Parabolic (c z : ℂ) (n : ℕ) : Prop := 0 < n ∧
  (iteratePoly c n).eval z = z ∧ ∃ q : ℕ, 0 < q ∧ multiplier c z n ^ q = 1

/-- The usual bounded-critical-orbit Mandelbrot set for z²+c. -/
def mandelbrot : Set ℂ := {c | Bornology.IsBounded (Set.range (fun n => (iteratePoly c n).eval 0))}

def parameters : Set ℂ := {c | c ∈ frontier mandelbrot ∧
  ∃ z : ℂ, ∃ n : ℕ, Parabolic c z n ∧
    ∃ ξ : ℝ, Liouville ξ ∧ multiplier c z n = (ξ : ℂ)}

theorem real_root_unity_not_liouville (ξ : ℝ) (q : ℕ) (hq : 0 < q)
    (hp : (ξ : ℂ) ^ q = 1) : ¬ Liouville ξ := by
  have hr : ξ ^ q = 1 := by
    apply Complex.ofReal_injective
    simpa using hp
  have ha : |ξ| = 1 := (abs_pow_eq_one ξ (Nat.ne_of_gt hq)).mp (by rw [hr]; simp)
  intro hL
  rcases le_total 0 ξ with hpos | hneg
  · rw [abs_of_nonneg hpos] at ha
    exact hL.irrational.ne_rat 1 (by simpa using ha)
  · rw [abs_of_nonpos hneg] at ha
    exact hL.irrational.ne_rat (-1) (by norm_num; linarith)

theorem no_parabolic_liouville_multiplier (c z : ℂ) (n : ℕ) (hp : Parabolic c z n) :
    ¬ ∃ ξ : ℝ, Liouville ξ ∧ multiplier c z n = (ξ : ℂ) := by
  rintro ⟨ξ, hL, hξ⟩
  rcases hp.2.2 with ⟨q, hq, hpow⟩
  rw [hξ] at hpow
  exact real_root_unity_not_liouville ξ q hq hpow hL

theorem parameters_empty : parameters = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro c ⟨hc, z, n, hp, hξ⟩
  exact no_parabolic_liouville_multiplier c z n hp hξ

theorem actual_dimension : dimH parameters = 0 := by rw [parameters_empty, dimH_empty]

theorem counterexample : parameters = ∅ ∧ dimH parameters = 0 ∧ dimH parameters ≠ 1 := by
  refine ⟨parameters_empty, actual_dimension, ?_⟩
  rw [actual_dimension]
  norm_num

end ParabolicMultiplierCounterexample
end

#print axioms ParabolicMultiplierCounterexample.iterate_eval
#print axioms ParabolicMultiplierCounterexample.multiplier_polynomial
#print axioms ParabolicMultiplierCounterexample.real_root_unity_not_liouville
#print axioms ParabolicMultiplierCounterexample.parameters_empty
#print axioms ParabolicMultiplierCounterexample.actual_dimension
#print axioms ParabolicMultiplierCounterexample.counterexample
