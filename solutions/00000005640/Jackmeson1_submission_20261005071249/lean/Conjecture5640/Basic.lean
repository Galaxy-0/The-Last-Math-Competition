import Mathlib

/-!
# Conjecture 00000005640 is false

Conjecture 00000005640 reads:

> Definition: The intersection spectrum and the intersection graph are two layers. Conjecture:
> There exist two convex-set families with the same intersection spectrum but non-isomorphic
> intersection graphs, and the separation is realized by an explicit redrawing pair preserving
> intersections.

The final clause asks for a *redrawing pair preserving intersections*: two families
`F : ι → Set E`, `G : κ → Set E'` together with a bijection `σ : ι ≃ κ` (the redrawing, sending
each member to its redrawn copy) such that, for distinct indices, `F i` and `F j` meet exactly when
`G (σ i)` and `G (σ j)` meet. Such a `σ` is an isomorphism of the intersection graphs, so a
redrawing pair preserving intersections never has non-isomorphic intersection graphs.

The term "intersection spectrum" is not defined in the source; it is left as an *arbitrary*
relation `SameSpectrum`, so the disproof holds whatever it means. The convex sets may live in
Euclidean spaces `EuclideanSpace ℝ (Fin d)` of any (possibly different) dimensions, and the index
types are arbitrary (finite or infinite).

Two further readings of "preserving intersections" are covered:
* the *nerve* reading (`σ` preserves non-emptiness of every finite sub-intersection), which
  implies the pairwise reading;
* a *one-sided* reading (intersecting members stay intersecting, new intersections may appear),
  for finite families whose intersection graphs have equally many edges. This holds when the
  intersection spectrum records the number of intersecting pairs, and in particular when it is
  the adjacency spectrum of the intersection graph (`oneSided_adjSpectrum_iso`).

The transport idea mirrors the accepted disproof of conjecture 00000005400
(solutions/00000005400, The Last Math Competition, GPL-3.0).
-/

namespace Conjecture5640

universe u v w z

/-- The intersection graph of an indexed family of sets: distinct indices are adjacent iff the
corresponding sets intersect. -/
def interGraph {ι : Type u} {E : Type v} (F : ι → Set E) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (F i ∩ F j).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Set.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem interGraph_adj {ι : Type u} {E : Type v} (F : ι → Set E) (i j : ι) :
    (interGraph F).Adj i j ↔ i ≠ j ∧ (F i ∩ F j).Nonempty := Iff.rfl

section Readings

variable {ι : Type u} {κ : Type w} {E : Type v} {E' : Type z}

/-- The redrawing `σ` of `F` as `G` preserves pairwise intersections of distinct members. -/
def PreservesInter (F : ι → Set E) (G : κ → Set E') (σ : ι ≃ κ) : Prop :=
  ∀ i j, i ≠ j → ((F i ∩ F j).Nonempty ↔ (G (σ i) ∩ G (σ j)).Nonempty)

/-- Nerve reading: `σ` preserves non-emptiness of every finite sub-intersection. -/
def PreservesNerve (F : ι → Set E) (G : κ → Set E') (σ : ι ≃ κ) : Prop :=
  ∀ s : Finset ι, (⋂ i ∈ s, F i).Nonempty ↔ (⋂ i ∈ s, G (σ i)).Nonempty

/-- One-sided reading: intersecting distinct members remain intersecting after the redrawing. -/
def KeepsInter (F : ι → Set E) (G : κ → Set E') (σ : ι ≃ κ) : Prop :=
  ∀ i j, i ≠ j → (F i ∩ F j).Nonempty → (G (σ i) ∩ G (σ j)).Nonempty

theorem PreservesNerve.preservesInter [DecidableEq ι] {F : ι → Set E} {G : κ → Set E'}
    {σ : ι ≃ κ} (h : PreservesNerve F G σ) : PreservesInter F G σ := by
  intro i j _
  simpa [Set.inter_comm] using h {i, j}

/-- **Key lemma.** An intersection-preserving redrawing is an isomorphism of intersection graphs. -/
def isoOfPreserves {F : ι → Set E} {G : κ → Set E'} (σ : ι ≃ κ) (h : PreservesInter F G σ) :
    interGraph F ≃g interGraph G where
  toEquiv := σ
  map_rel_iff' := by
    intro i j
    simp only [interGraph_adj, ne_eq, σ.injective.eq_iff]
    constructor
    · rintro ⟨hij, hg⟩; exact ⟨hij, (h i j hij).2 hg⟩
    · rintro ⟨hij, hf⟩; exact ⟨hij, (h i j hij).1 hf⟩

theorem nonempty_iso {F : ι → Set E} {G : κ → Set E'} (σ : ι ≃ κ) (h : PreservesInter F G σ) :
    Nonempty (interGraph F ≃g interGraph G) :=
  ⟨isoOfPreserves σ h⟩

/-- One-sided reading: for finite families with equally many intersecting pairs, a redrawing that
keeps every intersection preserves all intersections. -/
theorem preservesInter_of_keeps [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {F : ι → Set E} {G : κ → Set E'} (σ : ι ≃ κ) (h : KeepsInter F G σ)
    [DecidableRel (interGraph F).Adj] [DecidableRel (interGraph G).Adj]
    (hcard : (interGraph F).edgeFinset.card = (interGraph G).edgeFinset.card) :
    PreservesInter F G σ := by
  classical
  -- `H` = the graph of `G` pulled back along `σ`; the graph of `F` is a subgraph of it
  let H : SimpleGraph ι := (interGraph G).comap σ
  have hle : interGraph F ≤ H := fun i j hij => by
    rw [interGraph_adj] at hij
    show (interGraph G).Adj (σ i) (σ j)
    exact (interGraph_adj _ _ _).2 ⟨fun e => hij.1 (σ.injective e), h i j hij.1 hij.2⟩
  have hcardH : H.edgeFinset.card = (interGraph F).edgeFinset.card := by
    rw [hcard]; exact (SimpleGraph.Iso.comap σ (interGraph G)).card_edgeFinset_eq
  have hEq : interGraph F = H :=
    SimpleGraph.edgeFinset_inj.1 (Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.2 hle) hcardH.le)
  intro i j hij
  refine ⟨h i j hij, fun hg => ?_⟩
  have hH : H.Adj i j := (interGraph_adj _ _ _).2 ⟨fun e => hij (σ.injective e), hg⟩
  rw [← hEq, interGraph_adj] at hH
  exact hH.2

end Readings

/-! ## The conjecture's objects and its statement -/

/-- A family of convex sets in the Euclidean space `ℝ^d`, indexed by a type `ι`. -/
structure ConvexFamily (d : ℕ) where
  /-- index type of the family -/
  ι : Type
  /-- the members -/
  sets : ι → Set (EuclideanSpace ℝ (Fin d))
  /-- every member is convex -/
  convex : ∀ i, Convex ℝ (sets i)

/-- The intersection graph of a convex family. -/
abbrev ConvexFamily.graph {d : ℕ} (F : ConvexFamily d) : SimpleGraph F.ι := interGraph F.sets

/-- `G` is a redrawing of `F` preserving intersections. -/
def IsRedrawingPair {d d' : ℕ} (F : ConvexFamily d) (G : ConvexFamily d') : Prop :=
  ∃ σ : F.ι ≃ G.ι, PreservesInter F.sets G.sets σ

/-- The conjecture, with "same intersection spectrum" an arbitrary relation `SameSpectrum`:
two convex families with the same spectrum and non-isomorphic intersection graphs, forming a
redrawing pair preserving intersections. -/
def Statement (SameSpectrum : ∀ {d d' : ℕ}, ConvexFamily d → ConvexFamily d' → Prop) : Prop :=
  ∃ (d d' : ℕ) (F : ConvexFamily d) (G : ConvexFamily d'),
    SameSpectrum F G ∧ IsEmpty (F.graph ≃g G.graph) ∧ IsRedrawingPair F G

/-- Weaker form: some pair separates the layers, and (possibly another) explicit redrawing pair
preserving intersections has non-isomorphic intersection graphs. -/
def StatementSeparate (SameSpectrum : ∀ {d d' : ℕ}, ConvexFamily d → ConvexFamily d' → Prop) :
    Prop :=
  (∃ (d d' : ℕ) (F : ConvexFamily d) (G : ConvexFamily d'),
    SameSpectrum F G ∧ IsEmpty (F.graph ≃g G.graph)) ∧
  ∃ (d d' : ℕ) (F : ConvexFamily d) (G : ConvexFamily d'),
    IsRedrawingPair F G ∧ IsEmpty (F.graph ≃g G.graph)

/-- **Main theorem.** Every redrawing pair preserving intersections has isomorphic intersection
graphs. -/
theorem redrawing_iso {d d' : ℕ} (F : ConvexFamily d) (G : ConvexFamily d')
    (h : IsRedrawingPair F G) : Nonempty (F.graph ≃g G.graph) := by
  obtain ⟨σ, hσ⟩ := h
  exact nonempty_iso σ hσ

/-- **The conjecture is false**, whatever "same intersection spectrum" means. -/
theorem conjecture5640_false
    (SameSpectrum : ∀ {d d' : ℕ}, ConvexFamily d → ConvexFamily d' → Prop) :
    ¬ Statement SameSpectrum := by
  rintro ⟨d, d', F, G, -, hne, hr⟩
  obtain ⟨e⟩ := redrawing_iso F G hr
  exact hne.false e

/-- The weaker form (separating pair and redrawing pair allowed to differ) is false as well. -/
theorem conjecture5640_separate_false
    (SameSpectrum : ∀ {d d' : ℕ}, ConvexFamily d → ConvexFamily d' → Prop) :
    ¬ StatementSeparate SameSpectrum := by
  rintro ⟨-, d, d', F, G, hr, hne⟩
  obtain ⟨e⟩ := redrawing_iso F G hr
  exact hne.false e

/-- Nerve reading of "preserving intersections". -/
theorem nerve_redrawing_iso {d d' : ℕ} (F : ConvexFamily d) (G : ConvexFamily d')
    (σ : F.ι ≃ G.ι) (h : PreservesNerve F.sets G.sets σ) : Nonempty (F.graph ≃g G.graph) := by
  classical
  exact nonempty_iso σ h.preservesInter

/-- One-sided reading of "preserving intersections", for finite families with equally many
intersecting pairs. -/
theorem oneSided_redrawing_iso {d d' : ℕ} (F : ConvexFamily d) (G : ConvexFamily d')
    [Fintype F.ι] [Fintype G.ι] (σ : F.ι ≃ G.ι) (h : KeepsInter F.sets G.sets σ)
    [DecidableEq F.ι] [DecidableEq G.ι] [DecidableRel F.graph.Adj] [DecidableRel G.graph.Adj]
    (hcard : F.graph.edgeFinset.card = G.graph.edgeFinset.card) :
    Nonempty (F.graph ≃g G.graph) :=
  nonempty_iso σ (preservesInter_of_keeps σ h hcard)

/-! ### One-sided reading with the adjacency spectrum

If the "intersection spectrum" is the adjacency spectrum (characteristic polynomial of the
adjacency matrix) of the intersection graph, equal spectra force equally many edges, because
`trace (A * A) = 2 |E|` and `trace (A * A)` is the sum of the squared roots of the characteristic
polynomial (spectral theorem). -/

open Matrix in
/-- For a real symmetric matrix, `trace (A * A)` is determined by the characteristic polynomial. -/
theorem trace_mul_self_eq_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    (A * A).trace = (A.charpoly.roots.map (fun x => x ^ 2)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_mul, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, diagonal_mul_diagonal,
    trace_diagonal]
  simp [sq]

open Matrix in
theorem trace_adj_sq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (G.adjMatrix ℝ * G.adjMatrix ℝ).trace = 2 * G.edgeFinset.card := by
  simp only [trace, diag_apply, SimpleGraph.adjMatrix_mul_self_apply_self]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

open Matrix in
/-- Cospectral graphs (equal adjacency characteristic polynomials) have equally many edges. -/
theorem card_edges_eq_of_charpoly {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : (G.adjMatrix ℝ).charpoly = (H.adjMatrix ℝ).charpoly) :
    G.edgeFinset.card = H.edgeFinset.card := by
  have hG : (G.adjMatrix ℝ).IsHermitian := by
    show (G.adjMatrix ℝ)ᴴ = _
    ext i j; simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hH : (H.adjMatrix ℝ).IsHermitian := by
    show (H.adjMatrix ℝ)ᴴ = _
    ext i j; simp [SimpleGraph.adjMatrix_apply, H.adj_comm]
  have e1 := trace_mul_self_eq_roots hG
  have e2 := trace_mul_self_eq_roots hH
  rw [h] at e1
  rw [trace_adj_sq] at e1 e2
  have := e1.trans e2.symm
  exact_mod_cast (mul_right_inj' (two_ne_zero (α := ℝ))).1 this

/-- One-sided reading of "preserving intersections" with the adjacency-spectrum reading of
"same intersection spectrum": the intersection graphs are still isomorphic. -/
theorem oneSided_adjSpectrum_iso {d d' : ℕ} (F : ConvexFamily d) (G : ConvexFamily d')
    [Fintype F.ι] [Fintype G.ι] [DecidableEq F.ι] [DecidableEq G.ι]
    [DecidableRel F.graph.Adj] [DecidableRel G.graph.Adj]
    (hspec : (F.graph.adjMatrix ℝ).charpoly = (G.graph.adjMatrix ℝ).charpoly)
    (σ : F.ι ≃ G.ι) (h : KeepsInter F.sets G.sets σ) :
    Nonempty (F.graph ≃g G.graph) :=
  oneSided_redrawing_iso F G σ h (card_edges_eq_of_charpoly _ _ hspec)

/-- Non-vacuity: the conjecture's objects exist. Two copies of the whole line `ℝ^1` form a
convex family, and the identity redrawing preserves intersections. -/
def sampleFamily : ConvexFamily 1 where
  ι := Fin 2
  sets := fun _ => Set.univ
  convex := fun _ => convex_univ

theorem sample_redrawing : IsRedrawingPair sampleFamily sampleFamily :=
  ⟨Equiv.refl _, fun _ _ _ => Iff.rfl⟩

theorem sample_adj : sampleFamily.graph.Adj (0 : Fin 2) (1 : Fin 2) :=
  (interGraph_adj _ _ _).2 ⟨(by decide : (0 : Fin 2) ≠ 1), ⟨0, trivial, trivial⟩⟩

end Conjecture5640
