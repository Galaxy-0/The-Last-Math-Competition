import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

namespace ConstantCoupling

noncomputable section

-- Actual graphs in the real Hilbert line.
def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1 - q.1) (p.2 - q.2)

def MaximalMonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G

def constantOperator (c : ℝ) (_ : ℝ) : Set ℝ := {c}

def graph (c : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ constantOperator c p.1}

theorem inner_real (x y : ℝ) : inner (𝕜 := ℝ) x y = x * y := by
  simp [RCLike.inner_apply, mul_comm]

theorem graph_membership (c : ℝ) (p : ℝ × ℝ) : p ∈ graph c ↔ p.2 = c := by
  rfl

theorem constant_monotone (c : ℝ) : MonotoneGraph (graph c) := by
  intro p hp q hq
  have hp' := (graph_membership c p).mp hp
  have hq' := (graph_membership c q).mp hq
  simp [hp', hq']

-- Maximality is proved against every monotone graph extension.
theorem constant_maximal (c : ℝ) : MaximalMonotoneGraph (graph c) := by
  refine ⟨constant_monotone c, ?_⟩
  intro H hH hsub p hp
  have hleft : (p.1 - 1, c) ∈ H := hsub (by simp [graph, constantOperator])
  have hright : (p.1 + 1, c) ∈ H := hsub (by simp [graph, constantOperator])
  have hl := hH p hp (p.1 - 1, c) hleft
  have hr := hH p hp (p.1 + 1, c) hright
  rw [inner_real] at hl hr
  apply (graph_membership c p).mpr
  dsimp at hl hr
  nlinarith

def coupling : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem coupling_identity (x : ℝ) : coupling x = x := rfl

theorem coupling_positive (x : ℝ) :
    0 ≤ inner (𝕜 := ℝ) x (coupling x) := by
  rw [coupling_identity, inner_real]
  exact mul_self_nonneg x

-- The image-and-Minkowski-sum definition is the set-valued coupled operator.
def coupledValue (x y : ℝ) : Set ℝ :=
  {z | ∃ a ∈ constantOperator 1 x, ∃ b ∈ constantOperator 1 y,
    z = a + coupling b}

theorem coupled_value (x y : ℝ) : coupledValue x y = {2} := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, hz⟩
    have ha' : a = 1 := ha
    have hb' : b = 1 := hb
    simp [ha', hb', coupling_identity] at hz
    norm_num at hz ⊢
    exact hz
  · intro hz
    have hz' : z = 2 := hz
    refine ⟨1, rfl, 1, rfl, ?_⟩
    norm_num [coupling_identity]
    exact hz'

theorem no_solution_pairs : ¬ ∃ x y : ℝ, (0 : ℝ) ∈ coupledValue x y := by
  rintro ⟨x, y, h⟩
  rw [coupled_value] at h
  norm_num at h

theorem no_shared_input_solution : ¬ ∃ x : ℝ, (0 : ℝ) ∈ coupledValue x x := by
  rintro ⟨x, h⟩
  exact no_solution_pairs ⟨x, x, h⟩

theorem counterexample :
    MaximalMonotoneGraph (graph 1) ∧
    (∀ x, coupling x = x) ∧
    (¬ ∃ x y : ℝ, (0 : ℝ) ∈ coupledValue x y) ∧
    (¬ ∃ x : ℝ, (0 : ℝ) ∈ coupledValue x x) :=
  ⟨constant_maximal 1, coupling_identity, no_solution_pairs, no_shared_input_solution⟩

#print axioms constant_maximal
#print axioms coupling_positive
#print axioms coupled_value
#print axioms no_solution_pairs
#print axioms counterexample

end
end ConstantCoupling
