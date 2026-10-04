import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ResolventProof

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Monotonicity of the actual set-valued graph.
def MonotoneGraph (A : E → Set E) : Prop :=
  ∀ u v a b, a ∈ A u → b ∈ A v → 0 ≤ inner (𝕜 := ℝ) (u - v) (a - b)

-- x belongs to (I + lambda A)(u).
def Resolves (A : E → Set E) (lambda : ℝ) (x u : E) : Prop :=
  ∃ a ∈ A u, x = u + lambda • a

def Domain (A : E → Set E) (lambda : ℝ) : Set E :=
  {x | ∃ u, Resolves A lambda x u}

theorem firm_graph {A : E → Set E} (hA : MonotoneGraph A)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    {x y u v : E} (hx : Resolves A lambda x u) (hy : Resolves A lambda y v) :
    ‖u - v‖ ^ 2 ≤ inner (𝕜 := ℝ) (u - v) (x - y) := by
  obtain ⟨a, ha, hx⟩ := hx
  obtain ⟨b, hb, hy⟩ := hy
  have hm := hA u v a b ha hb
  have hid : inner (𝕜 := ℝ) (u - v) (x - y) =
      ‖u - v‖ ^ 2 + lambda * inner (𝕜 := ℝ) (u - v) (a - b) := by
    rw [← real_inner_self_eq_norm_sq, hx, hy]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    ring
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg hlambda hm)

theorem unique_value {A : E → Set E} (hA : MonotoneGraph A)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    {x u v : E} (hu : Resolves A lambda x u) (hv : Resolves A lambda x v) :
    u = v := by
  have hf := firm_graph hA hlambda hu hv
  simp only [sub_self, inner_zero_right] at hf
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def resolvent (A : E → Set E) (lambda : ℝ) (x : Domain A lambda) : E :=
  Classical.choose x.property

theorem resolvent_spec (A : E → Set E) (lambda : ℝ) (x : Domain A lambda) :
    Resolves A lambda x.val (resolvent A lambda x) :=
  Classical.choose_spec x.property

theorem graph_iff_value {A : E → Set E} (hA : MonotoneGraph A)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (x : Domain A lambda) (u : E) :
    Resolves A lambda x.val u ↔ u = resolvent A lambda x := by
  constructor
  · intro hu
    exact unique_value hA hlambda hu (resolvent_spec A lambda x)
  · intro hu
    rw [hu]
    exact resolvent_spec A lambda x

theorem resolvent_firm {A : E → Set E} (hA : MonotoneGraph A)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (x y : Domain A lambda) :
    ‖resolvent A lambda x - resolvent A lambda y‖ ^ 2 ≤
      inner (𝕜 := ℝ) (resolvent A lambda x - resolvent A lambda y) (x.val - y.val) :=
  firm_graph hA hlambda (resolvent_spec A lambda x) (resolvent_spec A lambda y)

theorem diagonal_iff_zero (A : E → Set E) {lambda : ℝ} (hlambda : 0 < lambda)
    (x : E) : Resolves A lambda x x ↔ (0 : E) ∈ A x := by
  constructor
  · rintro ⟨a, ha, heq⟩
    have hs : lambda • a = 0 := by
      have ht := congrArg (fun z : E => z - x) heq
      simpa using ht.symm
    have ha0 : a = 0 := (smul_eq_zero.mp hs).resolve_left (ne_of_gt hlambda)
    simpa [ha0] using ha
  · intro hzero
    exact ⟨0, hzero, by simp⟩

def FixedSet (A : E → Set E) (lambda : ℝ) : Set E :=
  {x | ∃ hx : x ∈ Domain A lambda, resolvent A lambda ⟨x, hx⟩ = x}

def ZeroSet (A : E → Set E) : Set E := {x | (0 : E) ∈ A x}

theorem fixed_set_eq_zero_set {A : E → Set E} (hA : MonotoneGraph A)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    FixedSet A lambda = ZeroSet A := by
  ext x
  constructor
  · rintro ⟨hx, hfix⟩
    have hr := resolvent_spec A lambda ⟨x, hx⟩
    rw [hfix] at hr
    exact (diagonal_iff_zero A hlambda x).mp hr
  · intro hzero
    have hr := (diagonal_iff_zero A hlambda x).mpr hzero
    have hx : x ∈ Domain A lambda := ⟨x, hr⟩
    exact ⟨hx, (unique_value hA hlambda.le (resolvent_spec A lambda ⟨x, hx⟩) hr)⟩

end
end ResolventProof

#print axioms ResolventProof.firm_graph
#print axioms ResolventProof.graph_iff_value
#print axioms ResolventProof.resolvent_firm
#print axioms ResolventProof.fixed_set_eq_zero_set
