import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
noncomputable section
namespace SummableTolerance

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

theorem lipschitz : LipschitzWith 1 (fun _ : ℝ => (1 : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_self, NNReal.coe_one, one_mul]
  exact dist_nonneg

def ResolventEquation (x y : ℝ) : Prop := ∃ a ∈ A y, x = y+a
def resolvent (x : ℝ) : ℝ := x-1
theorem actual_resolvent (x y : ℝ) :
    ResolventEquation x y ↔ y = resolvent x := by
  constructor
  · rintro ⟨a, ha, hx⟩
    have ha' : a = 1 := ha
    dsimp [resolvent]
    linarith
  · intro hy
    refine ⟨1, rfl, ?_⟩
    dsimp [resolvent] at hy
    linarith

def orbit (x : ℝ) (n : ℕ) : ℝ := resolvent^[n] x
def error (_ : ℕ) : ℝ := 0
def tolerance (_ : ℕ) : ℝ := 0

-- Standard additive-error inexact proximal inclusion, with unit proximal parameter.
def InexactPPA (u : ℕ → ℝ) (e eps : ℕ → ℝ) : Prop :=
  ∀ n, (∃ a ∈ A (u (n+1)), u n-u (n+1)-e n = a) ∧
    ‖e n‖ ≤ eps n

theorem actual_iterates (x : ℝ) (n : ℕ) : orbit x n = x-(n : ℝ) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hs : orbit x (n+1) = resolvent (orbit x n) :=
      Function.iterate_succ_apply' resolvent n x
    rw [hs, resolvent, ih]
    push_cast
    ring

theorem genuine_inexact_inclusion (x : ℝ) :
    InexactPPA (orbit x) error tolerance := by
  intro n
  constructor
  · refine ⟨1, rfl, ?_⟩
    rw [actual_iterates, actual_iterates]
    dsimp [error]
    push_cast
    ring
  · simp [error, tolerance]

theorem genuine_resolvent_steps (x : ℝ) (n : ℕ) :
    ResolventEquation (orbit x n) (orbit x (n+1)) := by
  rw [actual_resolvent]
  exact Function.iterate_succ_apply' resolvent n x

theorem summable_tolerances :
    (∀ n, 0 ≤ tolerance n) ∧ Summable tolerance ∧
    (∑' n, tolerance n) = 0 := by
  refine ⟨fun _ => le_rfl, ?_, ?_⟩
  · exact summable_zero
  · exact tsum_zero

theorem no_zero : ¬ ∃ x, (0 : ℝ) ∈ A x := by simp [A]

theorem no_strong_limit (x a : ℝ) : ¬ Tendsto (orbit x) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have he : (fun n => orbit x (n+1)-orbit x n) = fun _ => (-1 : ℝ) := by
      funext n
      rw [actual_iterates, actual_iterates]
      push_cast
      ring
    simpa [Function.comp_def, he] using hs.sub h
  have hz : (-1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at hz

theorem counterexample :
    MaximalMonotoneGraph graph ∧
    LipschitzWith 1 (fun _ : ℝ => (1 : ℝ)) ∧
    (∀ x y, ResolventEquation x y ↔ y = resolvent x) ∧
    ((∀ n, 0 ≤ tolerance n) ∧ Summable tolerance ∧ (∑' n, tolerance n) = 0) ∧
    (∀ x, InexactPPA (orbit x) error tolerance) ∧
    (∀ x n, ResolventEquation (orbit x n) (orbit x (n+1))) ∧
    (∀ x a, ¬ Tendsto (orbit x) atTop (𝓝 a)) ∧
    (¬ ∃ x, (0 : ℝ) ∈ A x) :=
  ⟨maximal, lipschitz, actual_resolvent, summable_tolerances,
    genuine_inexact_inclusion, genuine_resolvent_steps, no_strong_limit, no_zero⟩

#print axioms maximal
#print axioms lipschitz
#print axioms actual_resolvent
#print axioms actual_iterates
#print axioms genuine_inexact_inclusion
#print axioms genuine_resolvent_steps
#print axioms summable_tolerances
#print axioms no_strong_limit
#print axioms counterexample
end SummableTolerance
