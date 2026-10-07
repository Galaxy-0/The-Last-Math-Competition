import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
Disproof of conjecture 00000002712 with the clique complex of one edge.

The source conjecture quantifies over flag simplicial complexes; it does not
restrict to homology spheres or combinatorial polytopes.  The standard g-vector
of a d-rank simplicial complex is the initial half of the h-vector differences,
where h is obtained by the usual f-to-h polynomial transform.  The 1-simplex
is a connected, pure flag complex of rank d=2.  It has h=(1,0,0), hence its
truncated g-vector has g_1 = h_1-h_0 = -1.
-/

namespace FlagComplexGVectorCounterexample

abbrev Vertex := Fin 2

/-- The actual one-edge graph whose clique complex is the full 1-simplex. -/
def edgeGraph : SimpleGraph Vertex := SimpleGraph.completeGraph Vertex

/-- Faces of the clique complex of `edgeGraph`. -/
def IsClique (s : Finset Vertex) : Prop :=
  ∀ ⦃u v⦄, u ∈ s → v ∈ s → u ≠ v → edgeGraph.Adj u v

noncomputable def faceFinset : Finset (Finset Vertex) := by
  classical
  exact Finset.univ.filter IsClique

theorem faceFinset_eq_univ : faceFinset = Finset.univ := by
  classical
  ext s
  simp [faceFinset, IsClique, edgeGraph, SimpleGraph.completeGraph]

/-- Face membership is inherited by every subset, as required of a simplicial
complex. -/
theorem faces_downward {s t : Finset Vertex} (ht : t ∈ faceFinset)
    (hst : s ⊆ t) : s ∈ faceFinset := by
  classical
  rcases Finset.mem_filter.mp ht with ⟨_, htc⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro u v hu hv huv
  exact htc (hst hu) (hst hv) huv

/-- The clique complex is flag by its defining face criterion. -/
def IsFlagComplex : Prop :=
  ∀ s : Finset Vertex, IsClique s → s ∈ faceFinset

theorem edgeCliqueComplex_is_flag : IsFlagComplex := by
  classical
  intro s hs
  simp [faceFinset, hs]

/-- The 1-skeleton is connected. -/
theorem edgeGraph_connected : edgeGraph.Connected := by
  simp [edgeGraph]

/-- A facet is an inclusion-maximal face. -/
def IsFacet (s : Finset Vertex) : Prop :=
  s ∈ faceFinset ∧ ∀ t ∈ faceFinset, s ⊆ t → t ⊆ s

/-- Every facet is an edge, so the complex is pure of dimension one. -/
theorem facets_have_card_two (s : Finset Vertex) (hs : IsFacet s) : s.card = 2 := by
  have hsu : s ⊆ Finset.univ := Finset.subset_univ _
  have hu : Finset.univ ∈ faceFinset := by rw [faceFinset_eq_univ]; simp
  have hus : Finset.univ ⊆ s := hs.2 Finset.univ hu hsu
  have heq : s = Finset.univ := Finset.Subset.antisymm hsu hus
  rw [heq]
  simp

theorem whole_vertex_set_is_facet : IsFacet Finset.univ := by
  constructor
  · rw [faceFinset_eq_univ]
    simp
  · intro t ht hsub
    exact Finset.subset_univ _

/-- Purity: every inclusion-maximal face has the same cardinality. -/
def IsPure : Prop :=
  (∃ s, IsFacet s) ∧ ∀ s, IsFacet s → s.card = 2

theorem edgeCliqueComplex_is_pure : IsPure := by
  exact ⟨⟨Finset.univ, whole_vertex_set_is_facet⟩, facets_have_card_two⟩

/-- The largest face has two vertices, establishing rank `d=2` (dimension 1).
This is proved from the actual face set, not stipulated as f-vector data. -/
theorem face_sizes_have_maximum_two :
    (∀ s ∈ faceFinset, s.card ≤ 2) ∧ ∃ s ∈ faceFinset, s.card = 2 := by
  rw [faceFinset_eq_univ]
  constructor
  · intro s hs
    simpa using Finset.card_le_univ s
  · exact ⟨Finset.univ, by simp, by simp⟩

/-- The rank is the maximal cardinality of a face. -/
noncomputable def complexRank : ℕ := faceFinset.sup Finset.card

theorem complexRank_eq_two : complexRank = 2 := by
  rw [complexRank, faceFinset_eq_univ]
  decide

/-- Dimension is maximal face cardinality minus one. -/
noncomputable def complexDimension : ℕ := complexRank - 1

theorem complexDimension_eq_one : complexDimension = 1 := by
  simp [complexDimension, complexRank_eq_two]

/-- At rank d=2, the standard g-vector indices run from zero through one. -/
theorem gIndexCount_eq_two : complexRank / 2 + 1 = 2 := by
  simp [complexRank_eq_two]

/-- Number of actual faces with a specified cardinality. -/
noncomputable def faceCount (r : ℕ) : ℕ :=
  (faceFinset.filter fun s => s.card = r).card

theorem faceCount_empty_face : faceCount 0 = 1 := by
  rw [faceCount, faceFinset_eq_univ]
  decide

theorem faceCount_vertices : faceCount 1 = 2 := by
  rw [faceCount, faceFinset_eq_univ]
  decide

theorem faceCount_edges : faceCount 2 = 1 := by
  rw [faceCount, faceFinset_eq_univ]
  decide

theorem faceCount_three_vertex_faces : faceCount 3 = 0 := by
  rw [faceCount, faceFinset_eq_univ]
  decide

/-- The standard f-to-h transform for rank d=2:
`Σ_{j=0}^2 f_{j-1} (X-1)^(2-j)`. Here `f_{-1}=1` by convention, while
`f_0` and `f_1` are counted from `faceFinset`. -/
noncomputable def hPolynomial : Polynomial ℤ :=
  Polynomial.C (faceCount 0 : ℤ) * (Polynomial.X - 1) ^ complexRank +
    Polynomial.C (faceCount 1 : ℤ) * (Polynomial.X - 1) ^ (complexRank - 1) +
    Polynomial.C (faceCount 2 : ℤ) * (Polynomial.X - 1) ^ (complexRank - 2)

theorem hPolynomial_eq_X_sq : hPolynomial = Polynomial.X ^ 2 := by
  rw [hPolynomial, complexRank_eq_two, faceCount_empty_face,
    faceCount_vertices, faceCount_edges]
  norm_num
  ring

/-- h_i is the coefficient of X^(d-i), with d=2. -/
noncomputable def hEntry (i : ℕ) : ℤ := (hPolynomial.coeff (complexRank - i))

theorem hEntry_zero : hEntry 0 = 1 := by
  simp [hEntry, complexRank_eq_two, hPolynomial_eq_X_sq]

theorem hEntry_one : hEntry 1 = 0 := by
  simp [hEntry, complexRank_eq_two, hPolynomial_eq_X_sq]

theorem hEntry_two : hEntry 2 = 0 := by
  simp [hEntry, complexRank_eq_two, hPolynomial_eq_X_sq]

/-- The standard truncated g-vector: g_0=h_0 and g_i=h_i-h_(i-1).
For rank d=2 its valid indices are i=0,1, i.e. i≤floor(d/2). -/
noncomputable def gEntry (i : Fin (complexRank / 2 + 1)) : ℤ :=
  if i.val = 0 then hEntry 0 else hEntry i.val - hEntry (i.val - 1)

theorem gEntry_one_eq_neg_one :
    gEntry ⟨1, by rw [gIndexCount_eq_two]; decide⟩ = -1 := by
  norm_num [gEntry, hEntry_zero, hEntry_one]

theorem flag_g_nonnegativity_false :
    ¬ (∀ i : Fin (complexRank / 2 + 1), 0 ≤ gEntry i) := by
  intro h
  have hneg := gEntry_one_eq_neg_one
  have := h ⟨1, by rw [gIndexCount_eq_two]; decide⟩
  rw [hneg] at this
  norm_num at this

/-- A single edge gives a connected, pure, one-dimensional flag complex whose
actual standard truncated g-vector has a negative entry. -/
theorem actual_counterexample :
    edgeGraph.Connected ∧ IsFlagComplex ∧ IsPure ∧ complexDimension = 1 ∧
      gEntry ⟨1, by rw [gIndexCount_eq_two]; decide⟩ < 0 := by
  refine ⟨edgeGraph_connected, edgeCliqueComplex_is_flag,
    edgeCliqueComplex_is_pure, complexDimension_eq_one, ?_⟩
  rw [gEntry_one_eq_neg_one]
  norm_num

#print axioms faceFinset_eq_univ
#print axioms face_sizes_have_maximum_two
#print axioms complexRank_eq_two
#print axioms complexDimension_eq_one
#print axioms edgeGraph_connected
#print axioms facets_have_card_two
#print axioms edgeCliqueComplex_is_pure
#print axioms faceCount_vertices
#print axioms faceCount_edges
#print axioms hPolynomial_eq_X_sq
#print axioms gEntry_one_eq_neg_one
#print axioms flag_g_nonnegativity_false
#print axioms actual_counterexample

end FlagComplexGVectorCounterexample
