import Mathlib

/-!
# Conjecture 00000002718: a shellable 2-complex that is not 2-collapsible

The conjecture asserts (first conjunct) that a shellable `d`-dimensional complex is `d`-collapsible.
We refute this with `d = 2` and the boundary of the tetrahedron: all proper subsets of `Fin 4`.

* Simplicial complexes are finite set systems `K : Finset (Finset V)` closed under subsets.
* `d`-collapsibility is Wegner's notion, in the form stated by Tancer (arXiv:0808.1991): a face `σ` with
  `dim σ ≤ d - 1` that lies in a unique maximal face `τ` is removed together with the interval
  `[σ, τ] = {η ∈ K | σ ⊆ η ⊆ τ}`; `K` is `d`-collapsible if such steps reduce it to the empty complex.
* A shelling is an ordering `C₁, ..., C_t` of the maximal faces such that for every `k ≥ 2` the complex
  `(⋃_{i<k} ⟨Cᵢ⟩) ∩ ⟨C_k⟩` is pure of dimension `dim C_k - 1`.

The witness has no free face: every face that is not maximal lies in at least two maximal faces.
So every collapse-type move that needs a free face (Wegner `d`-collapses for `d ≤ 2`,
Whitehead collapses and elementary collapses) is impossible at the first step (`stuck_of_no_free_face`).
-/

namespace C2718

open Finset

section General

variable {V : Type*} [DecidableEq V]

/-- `K` is an (abstract, finite) simplicial complex: every subset of a face is a face. -/
def IsComplex (K : Finset (Finset V)) : Prop :=
  ∀ σ ∈ K, ∀ η ∈ σ.powerset, η ∈ K

/-- The maximal faces (facets) of `K`: faces contained in no strictly larger face. -/
def facets (K : Finset (Finset V)) : Finset (Finset V) :=
  K.filter (fun τ => ∀ η ∈ K, τ ⊆ η → η = τ)

/-- `K` is pure of dimension `d`: it is nonempty, every face has dimension at most `d`
(`card ≤ d + 1`), and every maximal face has dimension exactly `d` (`card = d + 1`). -/
def IsPureOfDim (K : Finset (Finset V)) (d : ℕ) : Prop :=
  K.Nonempty ∧ (∀ σ ∈ K, σ.card ≤ d + 1) ∧ ∀ τ ∈ facets K, τ.card = d + 1

/-- `τ` is the unique maximal face of `K` containing `σ`. -/
def UniqueMax (K : Finset (Finset V)) (σ τ : Finset V) : Prop :=
  τ ∈ facets K ∧ σ ⊆ τ ∧ ∀ τ' ∈ facets K, σ ⊆ τ' → τ' = τ

/-- `σ` is a free face of `K`: a face, different from the unique maximal face that contains it. -/
def IsFreeFace (K : Finset (Finset V)) (σ : Finset V) : Prop :=
  σ ∈ K ∧ ∃ τ, UniqueMax K σ τ ∧ σ ≠ τ

/-- Wegner's elementary `d`-collapse (Tancer's formulation): remove `[σ, τ(σ)]`, where
`dim σ = |σ| - 1 ≤ d - 1` and `τ(σ)` is the unique maximal face containing `σ`. -/
def ElemDCollapse (d : ℕ) (K K' : Finset (Finset V)) : Prop :=
  ∃ σ ∈ K, ((σ.card : ℤ) - 1 ≤ (d : ℤ) - 1) ∧
    ∃ τ, UniqueMax K σ τ ∧ K' = K.filter (fun η => ¬ (σ ⊆ η ∧ η ⊆ τ))

/-- `K` `d`-collapses to `L`: a finite sequence of elementary `d`-collapses. -/
def DCollapsesTo (d : ℕ) (K L : Finset (Finset V)) : Prop :=
  Relation.ReflTransGen (ElemDCollapse d) K L

/-- `K` is `d`-collapsible: it `d`-collapses to the empty complex. -/
def DCollapsible (d : ℕ) (K : Finset (Finset V)) : Prop :=
  DCollapsesTo d K ∅

/-- A (Whitehead) simplicial collapse: remove all `γ` with `τ ⊆ γ ⊆ σ`, where `τ ⊊ σ`, `σ` is
maximal and no other maximal face contains `τ`. -/
def SimplicialCollapse (K K' : Finset (Finset V)) : Prop :=
  ∃ τ ∈ K, ∃ σ, UniqueMax K τ σ ∧ τ ≠ σ ∧ K' = K.filter (fun γ => ¬ (τ ⊆ γ ∧ γ ⊆ σ))

/-- An elementary collapse: a simplicial collapse with `dim τ = dim σ - 1`. -/
def ElementaryCollapse (K K' : Finset (Finset V)) : Prop :=
  ∃ τ ∈ K, ∃ σ, UniqueMax K τ σ ∧ τ.card + 1 = σ.card ∧
    K' = K.filter (fun γ => ¬ (τ ⊆ γ ∧ γ ⊆ σ))

/-- Collapsible in Whitehead's sense: a sequence of simplicial collapses leads to a point
(the complex of a single vertex, `{∅, {v}}`). -/
def Collapsible (K : Finset (Finset V)) : Prop :=
  ∃ v : V, Relation.ReflTransGen SimplicialCollapse K {∅, {v}}

/-- The part of `⟨C_k⟩` covered by the earlier facets: `(⋃_{i<k} ⟨Cᵢ⟩) ∩ ⟨C_k⟩`. -/
def shellBoundary (L : List (Finset V)) (k : ℕ) (C : Finset V) : Finset (Finset V) :=
  C.powerset.filter (fun η => ∃ F ∈ L.take k, η ⊆ F)

/-- `B` is pure of dimension `m - 1` (i.e. all its maximal faces have `m` vertices) and nonempty. -/
def IsPureCard (B : Finset (Finset V)) (m : ℕ) : Prop :=
  B.Nonempty ∧ ∀ η ∈ facets B, η.card = m

/-- `L` is a shelling of `K`: it lists the maximal faces of `K`, each exactly once, and for every
`k ≥ 2` (0-based `k ≥ 1`) the complex `(⋃_{i<k} ⟨Cᵢ⟩) ∩ ⟨C_k⟩` is pure of dimension `dim C_k - 1`. -/
def IsShelling (K : Finset (Finset V)) (L : List (Finset V)) : Prop :=
  L.Nodup ∧ (∀ F ∈ L, F ∈ facets K) ∧ (∀ F ∈ facets K, F ∈ L) ∧
    ∀ k : Fin L.length, 0 < k.val →
      IsPureCard (shellBoundary L k.val (L.get k)) ((L.get k).card - 1)

/-- `K` is shellable: it admits a shelling. -/
def Shellable (K : Finset (Finset V)) : Prop :=
  ∃ L, IsShelling K L

/-- Robustness lemma: if every move of a relation `R` out of `K` needs a free face of `K`, and `K`
has no free face, then the only complex reachable from `K` by `R`-moves is `K` itself. -/
theorem stuck_of_no_free_face (R : Finset (Finset V) → Finset (Finset V) → Prop)
    (K : Finset (Finset V)) (hR : ∀ K', R K K' → ∃ σ, IsFreeFace K σ)
    (hK : ∀ σ, ¬ IsFreeFace K σ) {L : Finset (Finset V)} (h : Relation.ReflTransGen R K L) :
    L = K := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨K', hstep, _⟩
  · exact h.symm
  · obtain ⟨σ, hσ⟩ := hR K' hstep
    exact absurd hσ (hK σ)

theorem simplicialCollapse_needs_free (K K' : Finset (Finset V)) (h : SimplicialCollapse K K') :
    ∃ σ, IsFreeFace K σ := by
  obtain ⟨τ, hτ, σ, hu, hne, -⟩ := h
  exact ⟨τ, hτ, σ, hu, hne⟩

theorem elementaryCollapse_needs_free (K K' : Finset (Finset V)) (h : ElementaryCollapse K K') :
    ∃ σ, IsFreeFace K σ := by
  obtain ⟨τ, hτ, σ, hu, hc, -⟩ := h
  refine ⟨τ, hτ, σ, hu, ?_⟩
  rintro rfl
  omega

/-- On a complex whose maximal faces all have more than `d` vertices, every elementary
`d`-collapse uses a free face. -/
theorem elemDCollapse_needs_free (d : ℕ) (K K' : Finset (Finset V))
    (hfac : ∀ τ ∈ facets K, d < τ.card) (h : ElemDCollapse d K K') :
    ∃ σ, IsFreeFace K σ := by
  obtain ⟨σ, hσ, hdim, τ, hu, -⟩ := h
  refine ⟨σ, hσ, τ, hu, ?_⟩
  rintro rfl
  have := hfac σ hu.1
  omega

end General

/-! ## The witness: the boundary of the tetrahedron -/

/-- The boundary of the tetrahedron: all proper subsets of the vertex set `Fin 4`. -/
def tetraBoundary : Finset (Finset (Fin 4)) :=
  (univ : Finset (Fin 4)).powerset.erase univ

/-- The four triangles, in shelling order. -/
def shellingOrder : List (Finset (Fin 4)) :=
  [{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}]

theorem tetraBoundary_isComplex : IsComplex tetraBoundary := by
  unfold IsComplex tetraBoundary; decide

/-- The facets are exactly the four triangles. -/
theorem facets_tetraBoundary :
    facets tetraBoundary = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
  unfold facets tetraBoundary; decide

theorem tetraBoundary_pure : IsPureOfDim tetraBoundary 2 := by
  refine ⟨⟨∅, by unfold tetraBoundary; decide⟩, ?_, ?_⟩
  · unfold tetraBoundary; decide
  · rw [facets_tetraBoundary]; decide

theorem tetraBoundary_shelling : IsShelling tetraBoundary shellingOrder := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [facets_tetraBoundary]; decide
  · rw [facets_tetraBoundary]; decide
  · unfold IsPureCard shellBoundary facets shellingOrder; decide

theorem tetraBoundary_shellable : Shellable tetraBoundary :=
  ⟨shellingOrder, tetraBoundary_shelling⟩

/-- Every face of dimension at most 1 lies in at least two of the four triangles. -/
theorem two_facets_above :
    ∀ σ ∈ tetraBoundary, σ.card ≤ 2 →
      ∃ τ₁ ∈ facets tetraBoundary, ∃ τ₂ ∈ facets tetraBoundary, τ₁ ≠ τ₂ ∧ σ ⊆ τ₁ ∧ σ ⊆ τ₂ := by
  rw [facets_tetraBoundary]; unfold tetraBoundary; decide

/-- The tetrahedron boundary has no free face: no non-maximal face lies in a unique maximal face. -/
theorem tetraBoundary_no_free_face : ∀ σ, ¬ IsFreeFace tetraBoundary σ := by
  rintro σ ⟨hσ, τ, ⟨hτ, hστ, huniq⟩, hne⟩
  have hcard3 : ∀ F ∈ facets tetraBoundary, F.card = 3 := by
    rw [facets_tetraBoundary]; decide
  have hle : σ.card ≤ 2 := by
    have h1 : σ.card ≤ τ.card := card_le_card hστ
    have h2 : σ.card ≠ τ.card := fun h => hne (eq_of_subset_of_card_le hστ (le_of_eq h.symm))
    have := hcard3 τ hτ
    omega
  obtain ⟨τ₁, h₁, τ₂, h₂, h12, hs1, hs2⟩ := two_facets_above σ hσ hle
  exact h12 ((huniq τ₁ h₁ hs1).trans (huniq τ₂ h₂ hs2).symm)

theorem tetraBoundary_ne_empty : tetraBoundary ≠ ∅ := by
  unfold tetraBoundary; decide

/-- No elementary `d`-collapse (`d ≤ 2`) can start: the only complex reachable is the boundary. -/
theorem dCollapsesTo_eq (d : ℕ) (hd : d ≤ 2) {L : Finset (Finset (Fin 4))}
    (h : DCollapsesTo d tetraBoundary L) : L = tetraBoundary := by
  refine stuck_of_no_free_face _ _ (fun K' hK' => elemDCollapse_needs_free d _ K' ?_ hK')
    tetraBoundary_no_free_face h
  intro τ hτ
  rw [facets_tetraBoundary] at hτ
  have : τ.card = 3 := by revert τ; decide
  omega

/-- The boundary of the tetrahedron is not `d`-collapsible for any `d ≤ 2`. -/
theorem tetraBoundary_not_dCollapsible (d : ℕ) (hd : d ≤ 2) : ¬ DCollapsible d tetraBoundary :=
  fun h => tetraBoundary_ne_empty (dCollapsesTo_eq d hd h).symm

/-- Robustness: no simplicial (Whitehead) collapse can start, so the boundary is not collapsible
and does not collapse to any complex other than itself. -/
theorem tetraBoundary_simplicialCollapse_stuck {L : Finset (Finset (Fin 4))}
    (h : Relation.ReflTransGen SimplicialCollapse tetraBoundary L) : L = tetraBoundary :=
  stuck_of_no_free_face _ _ (fun K' hK' => simplicialCollapse_needs_free _ K' hK')
    tetraBoundary_no_free_face h

theorem tetraBoundary_elementaryCollapse_stuck {L : Finset (Finset (Fin 4))}
    (h : Relation.ReflTransGen ElementaryCollapse tetraBoundary L) : L = tetraBoundary :=
  stuck_of_no_free_face _ _ (fun K' hK' => elementaryCollapse_needs_free _ K' hK')
    tetraBoundary_no_free_face h

theorem tetraBoundary_not_collapsible : ¬ Collapsible tetraBoundary := by
  rintro ⟨v, h⟩
  have := tetraBoundary_simplicialCollapse_stuck h
  have hc := congrArg Finset.card this
  have h16 : tetraBoundary.card = 15 := by unfold tetraBoundary; decide
  have h2 : ({∅, {v}} : Finset (Finset (Fin 4))).card ≤ 2 := card_le_two
  omega

/-- The counterexample: a pure, shellable, 2-dimensional complex that is not 2-collapsible. -/
theorem counterexample :
    IsComplex tetraBoundary ∧ IsPureOfDim tetraBoundary 2 ∧ Shellable tetraBoundary ∧
      ¬ DCollapsible 2 tetraBoundary :=
  ⟨tetraBoundary_isComplex, tetraBoundary_pure, tetraBoundary_shellable,
    tetraBoundary_not_dCollapsible 2 le_rfl⟩

/-- **Conjecture 00000002718, first conjunct, is false**: "every shellable (finite, pure)
`d`-dimensional simplicial complex is `d`-collapsible" fails for `d = 2`. -/
theorem conjecture2718_false :
    ¬ ∀ (n d : ℕ) (K : Finset (Finset (Fin n))),
      IsComplex K → IsPureOfDim K d → Shellable K → DCollapsible d K :=
  fun h => tetraBoundary_not_dCollapsible 2 le_rfl
    (h 4 2 tetraBoundary tetraBoundary_isComplex tetraBoundary_pure tetraBoundary_shellable)

end C2718
