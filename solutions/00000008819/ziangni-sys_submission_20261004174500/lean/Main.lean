import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

noncomputable section
namespace ForwardBackwardCounterexample
open Filter
open scoped Topology

def f (x : ℝ) : ℝ := -x
def g (_ : ℝ) : ℝ := 0
def objective (x : ℝ) : ℝ := f x + g x

def epigraph (h : ℝ → ℝ) : Set (ℝ × ℝ) := {p | h p.1 ≤ p.2}
def ClosedConvex (h : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ h ∧ IsClosed (epigraph h)
-- Real-valued functions are finite everywhere: their extended-real versions
-- never equal minus infinity and have nonempty effective domain.
def Proper (h : ℝ → ℝ) : Prop := ∃ x : ℝ, (h x : EReal) < ⊤

theorem f_closed_convex : ClosedConvex f := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [f]
    nlinarith
  · exact isClosed_le continuous_fst.neg continuous_snd

theorem g_closed_convex : ClosedConvex g := by
  constructor
  · exact convexOn_const 0 convex_univ
  · exact isClosed_le continuous_const continuous_snd

theorem objective_eq : objective = f := by ext x; simp [objective, g]

theorem objective_closed_convex : ClosedConvex objective := by
  rw [objective_eq]
  exact f_closed_convex

theorem proper_functions : Proper f ∧ Proper g ∧ Proper objective := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> norm_num [f, g, objective]

theorem actual_gradient (x : ℝ) : gradient f x = -1 := by
  exact ((hasDerivAt_id x).neg.hasGradientAt').gradient

theorem gradient_lipschitz : LipschitzWith 1 (gradient f) := by
  intro x y
  simp [actual_gradient]

def Cocoercive (c : ℝ) (T : ℝ → ℝ) : Prop :=
  ∀ x y, c * ‖T x-T y‖^2 ≤ inner (𝕜 := ℝ) (T x-T y) (x-y)

theorem gradient_cocoercive : Cocoercive 1 (gradient f) := by
  intro x y
  simp [actual_gradient]

-- Genuine unit-step proximal objective and its complete minimizer relation.
def ProxObjective (y x : ℝ) : ℝ := g x + ‖x-y‖^2/2
def Prox (y x : ℝ) : Prop := ∀ z, ProxObjective y x ≤ ProxObjective y z

theorem prox_iff (y x : ℝ) : Prox y x ↔ x = y := by
  constructor
  · intro h
    have hh := h y
    simp [ProxObjective, g, Real.norm_eq_abs, sq_abs] at hh
    have hs := sq_nonneg (x-y)
    have he : x-y=0 := by nlinarith
    linarith
  · rintro rfl
    intro z
    simp [ProxObjective, g, Real.norm_eq_abs, sq_abs]
    positivity

theorem unique_prox (y : ℝ) : ∃! x, Prox y x :=
  ⟨y, (prox_iff y y).mpr rfl, fun x hx => (prox_iff y x).mp hx⟩

def proxMap (y : ℝ) : ℝ := y
theorem proxMap_actual (y : ℝ) : Prox y (proxMap y) := (prox_iff y y).mpr rfl

def step (x : ℝ) : ℝ := proxMap (x - (1:ℝ) * gradient f x)

theorem safe_step : (0:ℝ) < 1 ∧ (1:ℝ) < 2 / 1 := by norm_num

theorem step_eq (x : ℝ) : step x = x+1 := by
  simp [step, proxMap, actual_gradient]

theorem iterates (x : ℝ) (n : ℕ) : step^[n] x = x+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, step_eq]
    push_cast
    ring

theorem no_minimizer : ¬ ∃ x : ℝ, ∀ y, objective x ≤ objective y := by
  rintro ⟨x, hx⟩
  have h := hx (x+1)
  simp [objective, f, g] at h
  linarith

theorem not_convergent (x a : ℝ) : ¬ Tendsto (fun n : ℕ => step^[n] x) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 0) := by
    convert hs.sub h using 1 <;> norm_num
    ext n
    simp [iterates, step_eq]
  have he : (1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at he

def WeakLimit (x a : ℝ) : Prop := ∀ L : ℝ →L[ℝ] ℝ,
  Tendsto (fun n : ℕ => L (step^[n] x)) atTop (𝓝 (L a))

theorem not_weak (x a : ℝ) : ¬ WeakLimit x a := by
  intro h
  apply not_convergent x a
  simpa using h (ContinuousLinearMap.id ℝ ℝ)

theorem counterexample : ClosedConvex objective ∧ Proper objective ∧
    LipschitzWith 1 (gradient f) ∧ Cocoercive 1 (gradient f) ∧
    (∀ y, ∃! x, Prox y x) ∧ (∀ x a, ¬ Tendsto (fun n : ℕ => step^[n] x) atTop (𝓝 a)) :=
  ⟨objective_closed_convex, proper_functions.2.2, gradient_lipschitz,
    gradient_cocoercive, unique_prox, not_convergent⟩
end ForwardBackwardCounterexample
end
#print axioms ForwardBackwardCounterexample.objective_closed_convex
#print axioms ForwardBackwardCounterexample.actual_gradient
#print axioms ForwardBackwardCounterexample.unique_prox
#print axioms ForwardBackwardCounterexample.iterates
#print axioms ForwardBackwardCounterexample.counterexample
