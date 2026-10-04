import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
noncomputable section
namespace FBF

def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1-q.1) (p.2-q.2)
def MaximalMonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G
def constantGraph (c : ℝ) : Set (ℝ × ℝ) := {p | p.2 = c}
lemma real_inner (x y : ℝ) : inner (𝕜 := ℝ) x y = x*y := by
  simp [RCLike.inner_apply, mul_comm]

theorem constant_monotone (c : ℝ) : MonotoneGraph (constantGraph c) := by
  intro p hp q hq
  simp only [constantGraph, Set.mem_setOf_eq] at hp hq
  simp [hp, hq]

theorem constant_maximal (c : ℝ) : MaximalMonotoneGraph (constantGraph c) := by
  refine ⟨constant_monotone c, ?_⟩
  intro H hH hsub p hp
  have hl := hH p hp (p.1-1,c) (hsub (by simp [constantGraph]))
  have hr := hH p hp (p.1+1,c) (hsub (by simp [constantGraph]))
  rw [real_inner] at hl hr
  change p.2 = c
  dsimp at hl hr
  nlinarith

def A (_ : ℝ) : Set ℝ := {0}
def B (_ : ℝ) : ℝ := 1
def graphA : Set (ℝ × ℝ) := {p | p.2 ∈ A p.1}
def graphB : Set (ℝ × ℝ) := {p | p.2 = B p.1}

theorem A_maximal : MaximalMonotoneGraph graphA := constant_maximal 0
theorem B_maximal : MaximalMonotoneGraph graphB := constant_maximal 1

theorem joint_lipschitz :
    LipschitzWith 1 (fun _ : ℝ => (0 : ℝ)) ∧ LipschitzWith 1 B := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_self, NNReal.coe_one, one_mul]
    exact dist_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [B, dist_self, NNReal.coe_one, one_mul]
    exact dist_nonneg

def resolvent (_ : ℝ) (x : ℝ) : ℝ := x
def ResolventEquation (γ x y : ℝ) : Prop := ∃ a ∈ A y, x = y + γ*a

theorem actual_resolvent (γ x y : ℝ) : ResolventEquation γ x y ↔ y = resolvent γ x := by
  constructor
  · rintro ⟨a, ha, hx⟩
    have ha' : a = 0 := ha
    simp [ha'] at hx
    exact hx.symm
  · intro hy
    refine ⟨0, rfl, ?_⟩
    simp [resolvent] at hy
    simp [hy]

def firstForward (γ x : ℝ) : ℝ := x - γ*B x
def backward (γ x : ℝ) : ℝ := resolvent γ (firstForward γ x)
def lastForward (γ x : ℝ) : ℝ := backward γ x - γ*(B (backward γ x)-B x)
def step (γ x : ℝ) : ℝ := lastForward γ x

theorem genuine_backward_stage (γ x : ℝ) :
    ResolventEquation γ (firstForward γ x) (backward γ x) := by
  rw [actual_resolvent]
  rfl

theorem actual_step (γ x : ℝ) : step γ x = x - γ := by
  simp [step, lastForward, backward, resolvent, firstForward, B]

def inclusion (x : ℝ) : Set ℝ := {v | ∃ a ∈ A x, v = a+B x}
theorem no_zero : ¬ ∃ x : ℝ, (0 : ℝ) ∈ inclusion x := by
  rintro ⟨x,a,ha,h⟩
  have ha' : a = 0 := ha
  simp [B, ha'] at h

def orbit (γ x : ℝ) (n : ℕ) : ℝ := (step γ)^[n] x

theorem actual_iterates (γ x : ℝ) (n : ℕ) : orbit γ x n = x - (n : ℝ)*γ := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hs : orbit γ x (n+1) = step γ (orbit γ x n) :=
      Function.iterate_succ_apply' (step γ) n x
    rw [hs, actual_step, ih]
    push_cast
    ring

def WeaklyConverges (v : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ L : ℝ →L[ℝ] ℝ, Tendsto (fun n => L (v n)) atTop (𝓝 (L a))

theorem no_strong_limit (γ x a : ℝ) (hγ : γ ≠ 0) :
    ¬ Tendsto (orbit γ x) atTop (𝓝 a) := by
  intro h
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun _ : ℕ => -γ) atTop (𝓝 (0 : ℝ)) := by
    have he : (fun n => orbit γ x (n+1) - orbit γ x n) = fun _ => -γ := by
      funext n
      rw [actual_iterates, actual_iterates]
      push_cast
      ring
    simpa [Function.comp_def, he] using hshift.sub h
  have hz : -γ = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  exact hγ (neg_eq_zero.mp hz)

theorem no_weak_limit (γ x a : ℝ) (hγ : γ ≠ 0) :
    ¬ WeaklyConverges (orbit γ x) a := by
  intro h
  apply no_strong_limit γ x a hγ
  simpa using h (ContinuousLinearMap.id ℝ ℝ)

theorem safe_step : 0 < (1/2 : ℝ) ∧ (1/2 : ℝ)*1 < 1 := by norm_num

theorem counterexample :
    MaximalMonotoneGraph graphA ∧ MaximalMonotoneGraph graphB ∧
    (LipschitzWith 1 (fun _ : ℝ => (0 : ℝ)) ∧ LipschitzWith 1 B) ∧
    (∀ γ x y, ResolventEquation γ x y ↔ y = resolvent γ x) ∧
    (∀ γ x, ResolventEquation γ (firstForward γ x) (backward γ x)) ∧
    (0 < (1/2 : ℝ) ∧ (1/2 : ℝ)*1 < 1) ∧
    (∀ x n, orbit (1/2) x n = x - (n : ℝ)/2) ∧
    (∀ x a, ¬ WeaklyConverges (orbit (1/2) x) a) ∧
    (¬ ∃ x, (0 : ℝ) ∈ inclusion x) := by
  refine ⟨A_maximal, B_maximal, joint_lipschitz, actual_resolvent,
    genuine_backward_stage, safe_step, ?_, ?_, no_zero⟩
  · intro x n
    rw [actual_iterates]
    ring
  · intro x a
    exact no_weak_limit _ _ _ (by norm_num)

#print axioms A_maximal
#print axioms B_maximal
#print axioms joint_lipschitz
#print axioms actual_resolvent
#print axioms genuine_backward_stage
#print axioms actual_iterates
#print axioms no_weak_limit
#print axioms no_zero
#print axioms counterexample
end FBF
