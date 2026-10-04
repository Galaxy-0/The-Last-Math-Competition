import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
namespace ViscosityCounterexample
open Filter
open scoped Topology

def A (_ : ℝ) : Set ℝ := {1}
def graph : Set (ℝ × ℝ) := {p | p.2 ∈ A p.1}
def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1-q.1) (p.2-q.2)
def MaximalMonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G

theorem maximal : MaximalMonotoneGraph graph := by
  have hm : MonotoneGraph graph := by
    intro p hp q hq
    have hp' : p.2 = 1 := hp
    have hq' : q.2 = 1 := hq
    simp [hp', hq']
  refine ⟨hm, ?_⟩
  intro H hH hsub p hp
  have hl := hH p hp (p.1-1, 1) (hsub (by simp [graph, A]))
  have hr := hH p hp (p.1+1, 1) (hsub (by simp [graph, A]))
  simp only [RCLike.inner_apply, conj_trivial] at hl hr
  change p.2 = 1
  nlinarith

theorem no_zero (x : ℝ) : 0 ∉ A x := by simp [A]

def RootEquation (e x : ℝ) : Prop := ∃ a ∈ A x, a + e*x = 0

theorem root_iff (e x : ℝ) (he : 0 < e) : RootEquation e x ↔ x = -1/e := by
  have hne : e ≠ 0 := ne_of_gt he
  constructor
  · rintro ⟨a, ha, hx⟩
    have ha' : a = 1 := ha
    apply (eq_div_iff hne).mpr
    rw [ha'] at hx
    nlinarith
  · rintro rfl
    refine ⟨1, rfl, ?_⟩
    field_simp

theorem unique_root (e : ℝ) (he : 0 < e) : ∃! x, RootEquation e x :=
  ⟨-1/e, (root_iff e _ he).mpr rfl, fun x hx => (root_iff e x he).mp hx⟩

def epsilon (t : ℝ) : ℝ := 1/(t+1)
def roots (t : ℝ) : ℝ := -(t+1)
def flow (t : ℝ) : ℝ := -(t+1)/2

theorem epsilon_positive (t : ℝ) (ht : 0 ≤ t) : 0 < epsilon t := by
  unfold epsilon
  exact one_div_pos.mpr (by linarith)

theorem epsilon_limit : Tendsto epsilon atTop (𝓝 0) := by
  unfold epsilon
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id))

theorem roots_solve (t : ℝ) (ht : 0 ≤ t) : RootEquation (epsilon t) (roots t) := by
  refine ⟨1, rfl, ?_⟩
  have hn : t+1 ≠ 0 := by linarith
  dsimp [epsilon, roots]
  field_simp
  ring

theorem flow_derivative (t : ℝ) : HasDerivAt flow (-1/2) t := by
  convert ((hasDerivAt_id t).add_const 1).neg.div_const 2 using 1 <;> norm_num [flow]

/-- Genuine regularized differential inclusion: u'+a+epsilon*u=0 with a∈A(u). -/
theorem flow_equation (t : ℝ) (ht : 0 ≤ t) :
    ∃ a ∈ A (flow t), deriv flow t + a + epsilon t * flow t = 0 := by
  refine ⟨1, rfl, ?_⟩
  rw [(flow_derivative t).deriv]
  have hn : t+1 ≠ 0 := by linarith
  dsimp [epsilon, flow]
  field_simp
  ring

theorem affine_samples_not_convergent (d c a : ℝ) (hd : d ≠ 0) :
    ¬ Tendsto (fun n : ℕ => d*(n:ℝ)+c) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun _ : ℕ => d) atTop (𝓝 (0:ℝ)) := by
    convert hs.sub h using 1 <;> norm_num
    ext n
    push_cast
    ring
  have he : d = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  exact hd he

theorem roots_not_convergent (a : ℝ) : ¬ Tendsto roots atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  apply affine_samples_not_convergent (-1) (-1) a (by norm_num)
  convert hs using 1
  ext n
  simp [Function.comp_def, roots]
  ring

theorem flow_not_convergent (a : ℝ) : ¬ Tendsto flow atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  apply affine_samples_not_convergent (-1/2) (-1/2) a (by norm_num)
  convert hs using 1
  ext n
  simp [Function.comp_def, flow]
  ring

def WeakLimit (u : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun t => f (u t)) atTop (𝓝 (f a))

theorem roots_not_weak (a : ℝ) : ¬ WeakLimit roots a := by
  intro h
  apply roots_not_convergent a
  simpa using h (ContinuousLinearMap.id ℝ ℝ)

theorem flow_not_weak (a : ℝ) : ¬ WeakLimit flow a := by
  intro h
  apply flow_not_convergent a
  simpa using h (ContinuousLinearMap.id ℝ ℝ)

theorem counterexample : MaximalMonotoneGraph graph ∧
    (∀ e > 0, ∃! x, RootEquation e x) ∧ Tendsto epsilon atTop (𝓝 0) ∧
    (∀ t ≥ 0, RootEquation (epsilon t) (roots t)) ∧
    (∀ t ≥ 0, ∃ a ∈ A (flow t), deriv flow t+a+epsilon t*flow t=0) ∧
    (∀ a, ¬ Tendsto roots atTop (𝓝 a)) ∧ (∀ a, ¬ Tendsto flow atTop (𝓝 a)) :=
  ⟨maximal, unique_root, epsilon_limit, roots_solve, flow_equation,
    roots_not_convergent, flow_not_convergent⟩
end ViscosityCounterexample
end
#print axioms ViscosityCounterexample.maximal
#print axioms ViscosityCounterexample.unique_root
#print axioms ViscosityCounterexample.epsilon_limit
#print axioms ViscosityCounterexample.flow_derivative
#print axioms ViscosityCounterexample.flow_not_convergent
#print axioms ViscosityCounterexample.counterexample
