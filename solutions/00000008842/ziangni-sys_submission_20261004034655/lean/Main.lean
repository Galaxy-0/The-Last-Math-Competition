import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Constructions

namespace ClosedCompatibility

variable {X : Type*} [TopologicalSpace X]

def Pairwise (C : X → X → Prop) (G : Set X) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, C p q

def Maximal (C : X → X → Prop) (G : Set X) : Prop :=
  Pairwise C G ∧ ∀ T : Set X, Pairwise C T → G ⊆ T → T ⊆ G

omit [TopologicalSpace X] in
theorem membership {C : X → X → Prop} (hrefl : ∀ p, C p p)
    (hsymm : ∀ p q, C p q → C q p) {G : Set X} (hG : Maximal C G)
    (p : X) : p ∈ G ↔ ∀ q ∈ G, C p q := by
  constructor
  · exact fun hp => hG.1 p hp
  · intro hp
    have hT : Pairwise C (insert p G) := by
      intro r hr s hs
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        rcases Set.mem_insert_iff.mp hs with hs | hs
        · subst s
          exact hrefl p
        · exact hp s hs
      · rcases Set.mem_insert_iff.mp hs with hs | hs
        · subst s
          exact hsymm p r (hp r hr)
        · exact hG.1 r hr s hs
    exact hG.2 (insert p G) hT (Set.subset_insert p G) (Set.mem_insert p G)

theorem closed {C : X → X → Prop} (hrefl : ∀ p, C p p)
    (hsymm : ∀ p q, C p q → C q p)
    (hsection : ∀ q, IsClosed {p | C p q})
    {G : Set X} (hG : Maximal C G) : IsClosed G := by
  have heq : G = ⋂ q ∈ G, {p | C p q} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact membership hrefl hsymm hG p
  rw [heq]
  exact isClosed_iInter fun q => isClosed_iInter fun _ => hsection q

def closureInclusion (s : Set X) (x : s) : closure s :=
  ⟨x.val, subset_closure x.property⟩

theorem denseRange_closureInclusion (s : Set X) :
    DenseRange (closureInclusion s) := by
  have him : Subtype.val '' Set.range (closureInclusion s) = s := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      exact y.property
    · intro hx
      exact ⟨closureInclusion s ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  change Dense (Set.range (closureInclusion s))
  rw [Subtype.dense_iff, him]

end ClosedCompatibility

namespace MaximalMonotoneProof

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def PairMonotone (p q : E × E) : Prop :=
  0 ≤ inner (𝕜 := ℝ) (p.1 - q.1) (p.2 - q.2)

theorem pair_symm (p q : E × E) : PairMonotone p q ↔ PairMonotone q p := by
  unfold PairMonotone
  rw [← neg_sub q.1 p.1, ← neg_sub q.2 p.2]
  simp only [inner_neg_left, inner_neg_right, neg_neg]

def MonotoneGraph (G : Set (E × E)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, PairMonotone p q

-- Maximality under inclusion, not an assumed closedness property.
def MaximalMonotoneGraph (G : Set (E × E)) : Prop :=
  MonotoneGraph G ∧ ∀ T : Set (E × E), MonotoneGraph T → G ⊆ T → T ⊆ G

def Graph (A : E → Set E) : Set (E × E) := {p | p.2 ∈ A p.1}

def Domain (A : E → Set E) : Set E := {x | ∃ a, a ∈ A x}

theorem maximal_membership {G : Set (E × E)} (hG : MaximalMonotoneGraph G)
    (p : E × E) : p ∈ G ↔ ∀ q ∈ G, PairMonotone p q := by
  constructor
  · exact fun hp => hG.1 p hp
  · intro hp
    have hT : MonotoneGraph (insert p G) := by
      intro r hr s hs
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        rcases Set.mem_insert_iff.mp hs with hs | hs
        · subst s
          simp [PairMonotone]
        · exact hp s hs
      · rcases Set.mem_insert_iff.mp hs with hs | hs
        · subst s
          exact (pair_symm p r).mp (hp r hr)
        · exact hG.1 r hr s hs
    exact hG.2 (insert p G) hT (Set.subset_insert p G) (Set.mem_insert p G)

theorem maximal_graph_closed {G : Set (E × E)} (hG : MaximalMonotoneGraph G) :
    IsClosed G := by
  have heq : G = ⋂ q ∈ G, {p | PairMonotone p q} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact maximal_membership hG p
  rw [heq]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro hq
  exact isClosed_le continuous_const
    ((continuous_fst.sub continuous_const).inner (continuous_snd.sub continuous_const))

theorem conjecture_8842 (A : E → Set E) (hA : MaximalMonotoneGraph (Graph A)) :
    DenseRange (ClosedCompatibility.closureInclusion (Domain A)) ∧
      MaximalMonotoneGraph (Graph A) ∧ IsClosed (Graph A) :=
  ⟨ClosedCompatibility.denseRange_closureInclusion (Domain A), hA, maximal_graph_closed hA⟩

end
end MaximalMonotoneProof

namespace DualMonotoneProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def PairMonotone (p q : E × (E →L[ℝ] ℝ)) : Prop :=
  0 ≤ (p.2 - q.2) (p.1 - q.1)

theorem pair_refl (p : E × (E →L[ℝ] ℝ)) : PairMonotone p p := by
  simp [PairMonotone]

theorem pair_symm (p q : E × (E →L[ℝ] ℝ)) :
    PairMonotone p q → PairMonotone q p := by
  unfold PairMonotone
  rw [← neg_sub p.2 q.2, ← neg_sub p.1 q.1]
  simp only [ContinuousLinearMap.neg_apply, map_neg, neg_neg]
  exact id

theorem section_closed (q : E × (E →L[ℝ] ℝ)) :
    IsClosed {p | PairMonotone p q} :=
  isClosed_le continuous_const
    ((continuous_snd.sub continuous_const).clm_apply (continuous_fst.sub continuous_const))

def Graph (A : E → Set (E →L[ℝ] ℝ)) : Set (E × (E →L[ℝ] ℝ)) :=
  {p | p.2 ∈ A p.1}

def Domain (A : E → Set (E →L[ℝ] ℝ)) : Set E := {x | ∃ a, a ∈ A x}

-- The usual maximal monotonicity of an operator into the continuous dual.
def MaximalMonotone (A : E → Set (E →L[ℝ] ℝ)) : Prop :=
  ClosedCompatibility.Maximal PairMonotone (Graph A)

theorem graph_closed (A : E → Set (E →L[ℝ] ℝ)) (hA : MaximalMonotone A) :
    IsClosed (Graph A) :=
  ClosedCompatibility.closed pair_refl pair_symm section_closed hA

theorem conjecture_8842 (A : E → Set (E →L[ℝ] ℝ)) (hA : MaximalMonotone A) :
    DenseRange (ClosedCompatibility.closureInclusion (Domain A)) ∧
      ClosedCompatibility.Maximal PairMonotone (Graph A) ∧ IsClosed (Graph A) :=
  ⟨ClosedCompatibility.denseRange_closureInclusion (Domain A), hA, graph_closed A hA⟩

end DualMonotoneProof

#print axioms ClosedCompatibility.closed
#print axioms ClosedCompatibility.denseRange_closureInclusion
#print axioms MaximalMonotoneProof.maximal_membership
#print axioms MaximalMonotoneProof.maximal_graph_closed
#print axioms MaximalMonotoneProof.conjecture_8842
#print axioms DualMonotoneProof.conjecture_8842
