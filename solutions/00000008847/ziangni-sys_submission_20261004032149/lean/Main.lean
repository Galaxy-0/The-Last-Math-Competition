import Mathlib.Order.Zorn
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A complete proof of TLMC 00000008847 by a union-of-chains argument.
The argument works for arbitrary source/target types and any pairwise graph condition.
-/

namespace MaximalMonotone8847

variable {X Y : Type*}

/-- The ordinary graph of a set-valued operator. Empty values are permitted. -/
def graph (A : X → Set Y) : Set (X × Y) := {p | p.2 ∈ A p.1}

/-- Every subset of the product is the graph of a set-valued operator. -/
def ofGraph (s : Set (X × Y)) (x : X) : Set Y := {u | (x, u) ∈ s}

@[simp] theorem graph_ofGraph (s : Set (X × Y)) : graph (ofGraph s) = s := rfl

@[simp] theorem ofGraph_graph (A : X → Set Y) : ofGraph (graph A) = A := rfl

def Extends (A B : X → Set Y) : Prop := ∀ x, A x ⊆ B x

theorem graph_subset_iff (A B : X → Set Y) : graph A ⊆ graph B ↔ Extends A B := by
  constructor
  · intro h x u hu
    exact h (show (x, u) ∈ graph A from hu)
  · intro h p hp
    exact h p.1 hp

variable (C : (X × Y) → (X × Y) → Prop)

/-- An arbitrary pairwise condition on actual graph points. -/
def IsAdmissibleGraph (s : Set (X × Y)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, C p q

def IsAdmissible (A : X → Set Y) : Prop := IsAdmissibleGraph C (graph A)

theorem admissible_iff (A : X → Set Y) : IsAdmissible C A ↔
    ∀ (x y : X) (u v : Y), u ∈ A x → v ∈ A y → C (x, u) (y, v) := by
  constructor
  · intro h x y u v hu hv
    exact h (x, u) hu (y, v) hv
  · intro h p hp q hq
    exact h p.1 q.1 p.2 q.2 hp hq

/-- No proper admissible graph extension exists. -/
def IsMaximalAdmissible (A : X → Set Y) : Prop :=
  IsAdmissible C A ∧ ∀ B : X → Set Y, IsAdmissible C B → Extends A B → A = B

/-- A chain union preserves every pairwise graph condition. -/
theorem admissible_sUnion (c : Set (Set (X × Y)))
    (hc : IsChain (· ⊆ ·) c)
    (hm : ∀ s ∈ c, IsAdmissibleGraph C s) : IsAdmissibleGraph C (⋃₀ c) := by
  intro p hp q hq
  obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
  obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
  rcases hc.total hs ht with hst | hts
  · exact hm t ht p (hst hps) q hqt
  · exact hm s hs p hps q (hts hqt)

theorem exists_maximal_graph (s : Set (X × Y)) (hs : IsAdmissibleGraph C s) :
    ∃ m, s ⊆ m ∧ Maximal (IsAdmissibleGraph C) m := by
  apply zorn_subset_nonempty {t : Set (X × Y) | IsAdmissibleGraph C t} ?_ s hs
  intro c hc hchain _hne
  refine ⟨⋃₀ c, admissible_sUnion C c hchain (fun t ht => hc ht), ?_⟩
  intro t ht
  exact Set.subset_sUnion_of_mem ht

/-- Order-theoretic maximality and absence of proper admissible extensions coincide. -/
theorem maximal_graph_iff (A : X → Set Y) :
    Maximal (IsAdmissibleGraph C) (graph A) ↔ IsMaximalAdmissible C A := by
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
    have hmono : IsAdmissible C (ofGraph s) := by simpa [IsAdmissible] using hs
    have hext : Extends A (ofGraph s) :=
      (graph_subset_iff A (ofGraph s)).mp (by simpa using hAs)
    have heq := congrArg graph (hmax (ofGraph s) hmono hext)
    simpa using heq.symm.subset

/-- Every admissible set-valued map has a maximal admissible extension. -/
theorem exists_maximal_extension (A : X → Set Y) (hA : IsAdmissible C A) :
    ∃ B : X → Set Y, Extends A B ∧ IsMaximalAdmissible C B := by
  obtain ⟨s, hAs, hs⟩ := exists_maximal_graph C (graph A) hA
  refine ⟨ofGraph s, ?_, ?_⟩
  · exact (graph_subset_iff A (ofGraph s)).mp (by simpa using hAs)
  · apply (maximal_graph_iff C (ofGraph s)).mp
    simpa using hs

/-- Both clauses at arbitrary source/target types and arbitrary pairwise compatibility. -/
theorem conjecture_00000008847 :
    (∀ A : X → Set Y, IsAdmissible C A →
      ∃ B : X → Set Y, Extends A B ∧ IsMaximalAdmissible C B) ∧
    (∀ A : X → Set Y, Maximal (IsAdmissibleGraph C) (graph A) ↔ IsMaximalAdmissible C A) :=
  ⟨exists_maximal_extension C, maximal_graph_iff C⟩

namespace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def compatible (p q : E × E) : Prop :=
  0 ≤ @inner ℝ E _ (p.1 - q.1) (p.2 - q.2)

abbrev IsMonotone (A : E → Set E) : Prop := IsAdmissible compatible A
abbrev IsMaximalMonotone (A : E → Set E) : Prop := IsMaximalAdmissible compatible A

theorem monotone_iff (A : E → Set E) : IsMonotone A ↔
    ∀ x y u v : E, u ∈ A x → v ∈ A y →
      0 ≤ @inner ℝ E _ (x - y) (u - v) := admissible_iff compatible A

theorem result :
    (∀ A : E → Set E, IsMonotone A →
      ∃ B : E → Set E, Extends A B ∧ IsMaximalMonotone B) ∧
    (∀ A : E → Set E,
      Maximal (IsAdmissibleGraph compatible) (graph A) ↔ IsMaximalMonotone A) :=
  conjecture_00000008847 compatible

end InnerProduct

namespace Duality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine continuous-dual monotonicity, using evaluation of continuous linear maps. -/
def compatible (p q : E × (E →L[ℝ] ℝ)) : Prop :=
  0 ≤ (p.2 - q.2) (p.1 - q.1)

abbrev IsMonotone (A : E → Set (E →L[ℝ] ℝ)) : Prop := IsAdmissible compatible A
abbrev IsMaximalMonotone (A : E → Set (E →L[ℝ] ℝ)) : Prop :=
  IsMaximalAdmissible compatible A

theorem monotone_iff (A : E → Set (E →L[ℝ] ℝ)) : IsMonotone A ↔
    ∀ (x y : E) (u v : E →L[ℝ] ℝ), u ∈ A x → v ∈ A y →
      0 ≤ (u - v) (x - y) := admissible_iff compatible A

/-- Applies in particular to every real Banach space; completeness is unnecessary. -/
theorem result :
    (∀ A : E → Set (E →L[ℝ] ℝ), IsMonotone A →
      ∃ B : E → Set (E →L[ℝ] ℝ), Extends A B ∧ IsMaximalMonotone B) ∧
    (∀ A : E → Set (E →L[ℝ] ℝ),
      Maximal (IsAdmissibleGraph compatible) (graph A) ↔ IsMaximalMonotone A) :=
  conjecture_00000008847 compatible

end Duality

end MaximalMonotone8847

#print axioms MaximalMonotone8847.conjecture_00000008847
#print axioms MaximalMonotone8847.InnerProduct.result
#print axioms MaximalMonotone8847.Duality.result
