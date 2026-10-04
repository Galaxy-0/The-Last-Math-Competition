import Mathlib.Order.Zorn
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A complete proof of TLMC 00000008847 by a union-of-chains argument.
No completeness of the inner-product space is needed.
-/

namespace MaximalMonotone8847

variable {E : Type*}

/-- The ordinary graph of a set-valued operator. Empty values are permitted. -/
def graph (A : E → Set E) : Set (E × E) := {p | p.2 ∈ A p.1}

/-- Every subset of the product is the graph of a set-valued operator. -/
def ofGraph (s : Set (E × E)) (x : E) : Set E := {u | (x, u) ∈ s}

@[simp] theorem graph_ofGraph (s : Set (E × E)) : graph (ofGraph s) = s := rfl

@[simp] theorem ofGraph_graph (A : E → Set E) : ofGraph (graph A) = A := rfl

def Extends (A B : E → Set E) : Prop := ∀ x, A x ⊆ B x

theorem graph_subset_iff (A B : E → Set E) : graph A ⊆ graph B ↔ Extends A B := by
  constructor
  · intro h x u hu
    exact h (show (x, u) ∈ graph A from hu)
  · intro h p hp
    exact h p.1 hp

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The defining inner-product inequality for a monotone operator graph. -/
def IsMonotoneGraph (s : Set (E × E)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, 0 ≤ @inner ℝ E _ (p.1 - q.1) (p.2 - q.2)

def IsMonotone (A : E → Set E) : Prop := IsMonotoneGraph (graph A)

theorem monotone_iff (A : E → Set E) : IsMonotone A ↔
    ∀ x y u v : E, u ∈ A x → v ∈ A y → 0 ≤ @inner ℝ E _ (x - y) (u - v) := by
  constructor
  · intro h x y u v hu hv
    exact h (x, u) hu (y, v) hv
  · intro h p hp q hq
    exact h p.1 q.1 p.2 q.2 hp hq

/-- No proper monotone graph extension exists. -/
def IsMaximalMonotone (A : E → Set E) : Prop :=
  IsMonotone A ∧ ∀ B : E → Set E, IsMonotone B → Extends A B → A = B

/-- A chain union preserves the actual pairwise monotonicity inequality. -/
theorem monotone_sUnion (c : Set (Set (E × E)))
    (hc : IsChain (· ⊆ ·) c)
    (hm : ∀ s ∈ c, IsMonotoneGraph s) : IsMonotoneGraph (⋃₀ c) := by
  intro p hp q hq
  obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
  obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
  rcases hc.total hs ht with hst | hts
  · exact hm t ht p (hst hps) q hqt
  · exact hm s hs p hps q (hts hqt)

theorem exists_maximal_graph (s : Set (E × E)) (hs : IsMonotoneGraph s) :
    ∃ m, s ⊆ m ∧ Maximal IsMonotoneGraph m := by
  apply zorn_subset_nonempty {t : Set (E × E) | IsMonotoneGraph t} ?_ s hs
  intro c hc hchain _hne
  refine ⟨⋃₀ c, monotone_sUnion c hchain (fun t ht => hc ht), ?_⟩
  intro t ht
  exact Set.subset_sUnion_of_mem ht

/-- Order-theoretic maximality and operator maximal monotonicity coincide. -/
theorem maximal_graph_iff (A : E → Set E) :
    Maximal IsMonotoneGraph (graph A) ↔ IsMaximalMonotone A := by
  constructor
  · intro h
    refine ⟨h.prop, ?_⟩
    intro B hB hAB
    have hBA : graph B ⊆ graph A := h.2 hB ((graph_subset_iff A B).mpr hAB)
    have heq : graph A = graph B := Set.Subset.antisymm
      ((graph_subset_iff A B).mpr hAB) hBA
    exact congrArg ofGraph heq
  · rintro ⟨hA, hmax⟩
    refine ⟨hA, ?_⟩
    intro s hs hAs
    have hmono : IsMonotone (ofGraph s) := by simpa [IsMonotone] using hs
    have hext : Extends A (ofGraph s) :=
      (graph_subset_iff A (ofGraph s)).mp (by simpa using hAs)
    have heq := congrArg graph (hmax (ofGraph s) hmono hext)
    simpa using heq.symm.subset

/-- Every set-valued monotone operator admits a maximal monotone extension. -/
theorem exists_maximal_extension (A : E → Set E) (hA : IsMonotone A) :
    ∃ B : E → Set E, Extends A B ∧ IsMaximalMonotone B := by
  obtain ⟨s, hAs, hs⟩ := exists_maximal_graph (graph A) hA
  refine ⟨ofGraph s, ?_, ?_⟩
  · exact (graph_subset_iff A (ofGraph s)).mp (by simpa using hAs)
  · apply (maximal_graph_iff (ofGraph s)).mp
    simpa using hs

/-- Both assertions of the original conjecture, for arbitrary real inner-product spaces. -/
theorem conjecture_00000008847 :
    (∀ A : E → Set E, IsMonotone A →
      ∃ B : E → Set E, Extends A B ∧ IsMaximalMonotone B) ∧
    (∀ A : E → Set E, Maximal IsMonotoneGraph (graph A) ↔ IsMaximalMonotone A) :=
  ⟨exists_maximal_extension, maximal_graph_iff⟩

end MaximalMonotone8847

#print axioms MaximalMonotone8847.conjecture_00000008847
