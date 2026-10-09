import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology
namespace IHTNecessity
abbrev E := ℝ × ℝ
noncomputable def measurement : E →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
noncomputable def objective (p : E) : ℝ := (measurement p)^2/2
noncomputable def grad (p : E) : E := (p.1,0)
def sparse (p : E) : Prop := p.1=0 ∨ p.2=0
noncomputable def hardThreshold (p : E) : E := if |p.2| ≤ |p.1| then (p.1,0) else (0,p.2)
noncomputable def step (p : E) : E := hardThreshold (p-(1/2:ℝ) • grad p)
noncomputable def orbit (p : E) (n : ℕ) : E := step^[n] p
noncomputable def limitPoint (p : E) : E := (0,(step p).2)

theorem derivative (p : E) : HasFDerivAt objective (p.1 • measurement) p := by
  have hx : HasFDerivAt (fun q : E => q.1) measurement p := hasFDerivAt_fst
  convert ((hx.mul hx).const_mul (1/2:ℝ)) using 1
  · funext q; simp [objective, measurement]; ring
  · apply ContinuousLinearMap.ext; intro v; simp [measurement]; ring

theorem gradient_representation (p v : E) :
    (p.1 • measurement) v = (grad p).1*v.1+(grad p).2*v.2 := by simp [grad,measurement]

theorem threshold_sparse (p : E) : sparse (hardThreshold p) := by
  unfold hardThreshold sparse; split_ifs <;> simp

theorem threshold_nearest (p q : E) (hq : sparse q) :
    (p.1-(hardThreshold p).1)^2+(p.2-(hardThreshold p).2)^2 ≤
    (p.1-q.1)^2+(p.2-q.2)^2 := by
  unfold hardThreshold
  split_ifs with h
  · have hs : p.2^2 ≤ p.1^2 := (sq_le_sq).mpr h
    rcases hq with hq|hq <;> simp only [hq, sub_self, zero_pow, zero_add, sub_zero] <;>
      nlinarith [sq_nonneg (p.1-q.1), sq_nonneg (p.2-q.2)]
  · have hs : p.1^2 ≤ p.2^2 := (sq_le_sq).mpr (le_of_lt (lt_of_not_ge h))
    rcases hq with hq|hq <;> simp only [hq, sub_self, zero_pow, add_zero, sub_zero] <;>
      nlinarith [sq_nonneg (p.1-q.1), sq_nonneg (p.2-q.2)]

theorem step_formula (p : E) : step p = hardThreshold (p.1/2,p.2) := by
  unfold step grad; congr 1; ext <;> simp <;> ring
@[simp] theorem step_x (a : ℝ) : step (a,0) = (a/2,0) := by
  rw [step_formula]; simp [hardThreshold]
@[simp] theorem step_y (b : ℝ) : step (0,b) = (0,b) := by
  rw [step_formula]; unfold hardThreshold; split_ifs <;> simp_all

theorem axis_iterates (a b : ℝ) (n : ℕ) :
    step^[n] (a,0) = ((1/2:ℝ)^n*a,0) ∧ step^[n] (0,b) = (0,b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, ih.2]
    simp [pow_succ]; ring

theorem orbit_formula (p : E) (n : ℕ) :
    orbit p (n+1) = ((1/2:ℝ)^n*(step p).1,(step p).2) := by
  unfold orbit
  rw [Function.iterate_succ_apply]
  have h : step p = (p.1/2,0) ∨ step p = (0,p.2) := by
    rw [step_formula]; unfold hardThreshold; split_ifs <;> simp
  rcases h with h|h
  · rw [h,(axis_iterates (p.1/2) p.2 n).1]
  · rw [h,(axis_iterates (p.1/2) p.2 n).2]; simp

theorem limit_is_sparse_global_minimizer (p : E) :
    sparse (limitPoint p) ∧ objective (limitPoint p)=0 ∧ ∀ q : E, objective (limitPoint p) ≤ objective q := by
  simp [limitPoint,sparse,objective,measurement]
  intro q; positivity

theorem geometric_error (p : E) (n : ℕ) :
    ‖orbit p (n+1)-limitPoint p‖ = (1/2:ℝ)^n*|(step p).1| := by
  rw [orbit_formula]
  simp [limitPoint, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)]

theorem every_orbit_converges (p : E) : Tendsto (orbit p) atTop (𝓝 (limitPoint p)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp_rw [orbit_formula]
  have hpow : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [limitPoint] using (hpow.mul_const (step p).1).prodMk_nhds (tendsto_const_nhds (x:=(step p).2))

-- The genuine Euclidean restricted-curvature inequality on sparse points.
def RestrictedStrongConvexity (μ : ℝ) : Prop :=
  ∀ u v : E, sparse u → sparse v →
    objective u + (u.1 • measurement) (v-u) + μ/2*((v.1-u.1)^2+(v.2-u.2)^2) ≤ objective v

theorem no_positive_restricted_curvature : ¬ ∃ μ : ℝ, 0<μ ∧ RestrictedStrongConvexity μ := by
  rintro ⟨μ,hμ,h⟩
  have hx := h (0,0) (0,1) (by simp [sparse]) (by simp [sparse])
  norm_num [objective,measurement] at hx
  linarith

#print axioms derivative
#print axioms gradient_representation
#print axioms threshold_sparse
#print axioms threshold_nearest
#print axioms axis_iterates
#print axioms orbit_formula
#print axioms limit_is_sparse_global_minimizer
#print axioms geometric_error
#print axioms every_orbit_converges
#print axioms no_positive_restricted_curvature
end IHTNecessity
