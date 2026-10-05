import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

noncomputable section
namespace BregmanCounterexample
open Filter
open scoped Topology

def f (x : ℝ) : ℝ := -x
def mirror (x : ℝ) : ℝ := x^2/2

def epigraph (h : ℝ → ℝ) : Set (ℝ × ℝ) := {p | h p.1 ≤ p.2}
def ClosedConvex (h : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ h ∧ IsClosed (epigraph h)
def Proper (h : ℝ → ℝ) : Prop := ∃ x : ℝ, (h x : EReal) < ⊤

theorem f_properties : ClosedConvex f ∧ Proper f := by
  refine ⟨⟨?_, isClosed_le continuous_fst.neg continuous_snd⟩, ⟨0, ?_⟩⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [f]
    nlinarith
  · norm_num [f]

theorem mirror_properties : ClosedConvex mirror ∧ Proper mirror := by
  refine ⟨⟨?_, ?_⟩, ⟨0, ?_⟩⟩
  · simpa [mirror, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ConvexOn.smul (by norm_num : (0:ℝ) ≤ 1/2)
        (Even.convexOn_pow (by decide : Even (2:ℕ)) :
          ConvexOn ℝ Set.univ (fun x:ℝ => x^2))
  · apply isClosed_le _ continuous_snd
    change Continuous (fun p:ℝ×ℝ => p.1^2/2)
    fun_prop
  · norm_num [mirror]

theorem mirror_gradient (x : ℝ) : gradient mirror x = x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).hasGradientAt'.gradient using 1 <;>
    norm_num

def bregman (y x : ℝ) : ℝ :=
  mirror y - mirror x - inner (𝕜:=ℝ) (gradient mirror x) (y-x)

theorem bregman_eq (y x : ℝ) : bregman y x = (y-x)^2/2 := by
  simp only [bregman, mirror_gradient, mirror, RCLike.inner_apply, conj_trivial]
  ring

theorem bregman_properties (y x : ℝ) : 0 ≤ bregman y x ∧
    (bregman y x = 0 ↔ y=x) := by
  rw [bregman_eq]
  constructor
  · positivity
  · constructor
    · intro h; have := sq_nonneg (y-x); nlinarith
    · rintro rfl; simp

-- The true subgradient inequality is quantified over every competitor.
def Subgradient (x v : ℝ) : Prop := ∀ z, v*(z-x) ≤ f z-f x

theorem subgradient_iff (x v : ℝ) : Subgradient x v ↔ v = -1 := by
  constructor
  · intro h
    have hl := h (x-1)
    have hr := h (x+1)
    dsimp [f] at hl hr
    nlinarith
  · rintro rfl; intro z; dsimp [f]; linarith

def graph : Set (ℝ×ℝ) := {p | Subgradient p.1 p.2}
def MonotoneGraph (G : Set (ℝ×ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜:=ℝ) (p.1-q.1) (p.2-q.2)
def MaximalMonotoneGraph (G : Set (ℝ×ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G

theorem maximal : MaximalMonotoneGraph graph := by
  have hm : MonotoneGraph graph := by
    intro p hp q hq
    have hp' := (subgradient_iff p.1 p.2).mp hp
    have hq' := (subgradient_iff q.1 q.2).mp hq
    simp [hp',hq']
  refine ⟨hm, ?_⟩
  intro H hH hsub p hp
  have hl := hH p hp (p.1-1,-1) (hsub ((subgradient_iff _ _).mpr rfl))
  have hr := hH p hp (p.1+1,-1) (hsub ((subgradient_iff _ _).mpr rfl))
  simp only [RCLike.inner_apply, conj_trivial] at hl hr
  exact (subgradient_iff _ _).mpr (by nlinarith)

-- Unit-penalty Bregman proximal subproblem with its full argmin relation.
def proxObjective (x y : ℝ) : ℝ := f y + bregman y x
def Prox (x y : ℝ) : Prop := ∀ z, proxObjective x y ≤ proxObjective x z

theorem gap (x z : ℝ) : proxObjective x z - proxObjective x (x+1) =
    (z-(x+1))^2/2 := by
  simp only [proxObjective, f, bregman_eq]
  ring

theorem prox_iff (x y : ℝ) : Prox x y ↔ y=x+1 := by
  constructor
  · intro h
    have hh := h (x+1)
    have hg := gap x y
    have hs := sq_nonneg (y-(x+1))
    have he : y-(x+1)=0 := by nlinarith
    linarith
  · rintro rfl
    intro z
    have hg := gap x z
    have hs := sq_nonneg (z-(x+1))
    linarith

def step (x : ℝ) : ℝ := x+1

theorem unique_prox (x : ℝ) : ∃! y, Prox x y :=
  ⟨step x, (prox_iff _ _).mpr rfl, fun y hy => (prox_iff _ _).mp hy⟩

theorem exact_inclusion (x : ℝ) : Subgradient (step x) (-1) ∧
    gradient mirror (step x) - gradient mirror x + (-1) = 0 := by
  constructor
  · exact (subgradient_iff _ _).mpr rfl
  · simp [mirror_gradient,step]

def EpsilonSubgradient (y v e : ℝ) : Prop :=
  ∀ z, v*(z-y)-e ≤ f z-f y

def RelativeError (sigma x y v e : ℝ) : Prop :=
  0 ≤ e ∧ EpsilonSubgradient y v e ∧
    ‖v+y-x‖^2+2*e ≤ sigma^2*‖y-x‖^2

theorem zero_relative_error (x sigma : ℝ) : RelativeError sigma x (step x) (-1) 0 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro z; simpa using exact_inclusion x |>.1 z
  · simp only [step]
    have he : (-1:ℝ)+(x+1)-x=0 := by ring
    rw [he]
    simp
    positivity

theorem iterates (x : ℝ) (n : ℕ) : step^[n] x = x+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, Nat.cast_add, Nat.cast_one]
    ring

theorem no_minimizer : ¬ ∃ x : ℝ, ∀ y, f x ≤ f y := by
  rintro ⟨x, hx⟩
  have h := hx (x+1)
  dsimp [f] at h
  linarith

theorem not_convergent (x a : ℝ) : ¬ Tendsto (fun n:ℕ => step^[n] x) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun _:ℕ => (1:ℝ)) atTop (𝓝 0) := by
    convert hs.sub h using 1 <;> norm_num
    ext n
    simp [iterates,step]
  have he : (1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at he

theorem not_weak (x a : ℝ) : ¬ (∀ F : ℝ →L[ℝ] ℝ,
    Tendsto (fun n:ℕ => F (step^[n] x)) atTop (𝓝 (F a))) := by
  intro h
  apply not_convergent x a
  simpa using h (ContinuousLinearMap.id ℝ ℝ)

end BregmanCounterexample
#print axioms BregmanCounterexample.f_properties
#print axioms BregmanCounterexample.mirror_properties
#print axioms BregmanCounterexample.bregman_properties
#print axioms BregmanCounterexample.maximal
#print axioms BregmanCounterexample.unique_prox
#print axioms BregmanCounterexample.zero_relative_error
#print axioms BregmanCounterexample.not_convergent
#print axioms BregmanCounterexample.not_weak
