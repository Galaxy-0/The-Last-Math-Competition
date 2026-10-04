/-!
# Conjecture 00000002141: cospectral regular pairs of order 10 are not unique

The conjecture claims that the minimal order of a cospectral regular pair
is 10 and that the cospectral regular pair of order 10 is unique.  We exhibit
two cospectral pairs of 4-regular graphs on 10 vertices, `(A1, B1)` and
`(A2, B2)`, such that the graphs in each pair are non-isomorphic and the two pairs
are different (in fact `A1` is isomorphic to neither `A2` nor `B2`).

Graphs on the vertex set `{0, …, 9}` are Boolean adjacency functions.
Cospectrality is expressed through closed walks: for an `n`-vertex graph,
`tr(A^k) = Σ λᵢ^k`, and the power sums for `k = 1, …, n` determine the
spectrum (Newton's identities), so two graphs on 10 vertices are cospectral iff
they have the same number of closed walks of each length `k ≤ 10`.
-/

namespace Cospectral

/-- A graph on `{0, …, 9}`. -/
abbrev Graph := Nat → Nat → Bool

def ofEdges (l : List (Nat × Nat)) : Graph := fun u v =>
  l.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def A1 : Graph := ofEdges [(0,3),(0,5),(0,7),(0,9),(1,4),(1,5),(1,7),(1,9),(2,5),(2,6),
  (2,7),(2,8),(3,6),(3,8),(3,9),(4,6),(4,8),(4,9),(5,7),(6,8)]
def B1 : Graph := ofEdges [(0,3),(0,5),(0,7),(0,8),(1,4),(1,5),(1,8),(1,9),(2,5),(2,6),
  (2,7),(2,9),(3,6),(3,7),(3,8),(4,6),(4,8),(4,9),(5,7),(6,9)]
def A2 : Graph := ofEdges [(0,3),(0,5),(0,7),(0,8),(1,4),(1,5),(1,7),(1,9),(2,5),(2,6),
  (2,8),(2,9),(3,6),(3,7),(3,8),(4,6),(4,8),(4,9),(5,7),(6,9)]
def B2 : Graph := ofEdges [(0,3),(0,4),(0,6),(0,7),(1,5),(1,6),(1,8),(1,9),(2,5),(2,7),
  (2,8),(2,9),(3,4),(3,6),(3,7),(4,8),(4,9),(5,7),(5,8),(6,9)]

/-! ## Basic properties -/

/-- Simple graph: symmetric and loopless. -/
def IsSimple (g : Graph) : Prop :=
  ∀ u, u < 10 → ∀ v, v < 10 → g u v = g v u ∧ g u u = false

def degree (g : Graph) (u : Nat) : Nat := (List.range 10).countP (g u ·)

def Regular (g : Graph) (k : Nat) : Prop := ∀ u, u < 10 → degree g u = k

/-- Adjacency matrix as a list of rows (natural-number entries). -/
def adjMat (g : Graph) : List (List Nat) :=
  (List.range 10).map fun u => (List.range 10).map fun v => if g u v then 1 else 0

def entry (M : List (List Nat)) (i j : Nat) : Nat := (M.getD i []).getD j 0

def matMul (M N : List (List Nat)) : List (List Nat) :=
  (List.range 10).map fun i => (List.range 10).map fun j =>
    ((List.range 10).map fun l => entry M i l * entry N l j).foldr (· + ·) 0

def idMat : List (List Nat) :=
  (List.range 10).map fun i => (List.range 10).map fun j => if i = j then 1 else 0

def matPow (M : List (List Nat)) : Nat → List (List Nat)
  | 0 => idMat
  | k + 1 => matMul (matPow M k) M

def trace (M : List (List Nat)) : Nat :=
  ((List.range 10).map fun i => entry M i i).foldr (· + ·) 0

/-- Number of closed walks of length `k` = `tr(A^k)`. -/
def closedWalks (g : Graph) (k : Nat) : Nat := trace (matPow (adjMat g) k)

/-- Same adjacency spectrum (10 vertices): equal closed-walk counts for `k ≤ 10`. -/
def Cospectral (g h : Graph) : Prop := ∀ k, k ≤ 10 → closedWalks g k = closedWalks h k

/-- Graph isomorphism of graphs on `{0, …, 9}`. -/
def Iso (g h : Graph) : Prop :=
  ∃ σ τ : Nat → Nat,
    (∀ x, x < 10 → σ x < 10 ∧ τ (σ x) = x) ∧
    (∀ y, y < 10 → τ y < 10 ∧ σ (τ y) = y) ∧
    ∀ u, u < 10 → ∀ v, v < 10 → g u v = h (σ u) (σ v)

theorem iso_symm {g h : Graph} : Iso g h → Iso h g := by
  rintro ⟨σ, τ, hσ, hτ, hgh⟩
  refine ⟨τ, σ, hτ, hσ, fun u hu v hv => ?_⟩
  have := hgh (τ u) (hτ u hu).1 (τ v) (hτ v hv).1
  rw [(hτ u hu).2, (hτ v hv).2] at this
  exact this.symm

/-! ## Isomorphism invariants -/

/-- `uv` is an edge lying in no triangle. -/
def NT (g : Graph) (u v : Nat) : Prop :=
  g u v = true ∧ ∀ w, w < 10 → ¬(g u w = true ∧ g v w = true)

/-- Some edge lies in no triangle. -/
def HasNT (g : Graph) : Prop := ∃ u, u < 10 ∧ ∃ v, v < 10 ∧ NT g u v

/-- Some triangle-free edge `uv` shares no endpoint with another triangle-free edge. -/
def HasIsolatedNT (g : Graph) : Prop :=
  ∃ u, u < 10 ∧ ∃ v, v < 10 ∧ NT g u v ∧
    ∀ w, w < 10 → (w ≠ v → ¬ NT g u w) ∧ (w ≠ u → ¬ NT g v w)

instance (g : Graph) : Decidable (IsSimple g) := by unfold IsSimple; infer_instance
instance (g : Graph) (k : Nat) : Decidable (Regular g k) := by unfold Regular; infer_instance
instance (g h : Graph) : Decidable (Cospectral g h) := by unfold Cospectral; infer_instance
instance (g : Graph) (u v : Nat) : Decidable (NT g u v) := by unfold NT; infer_instance
instance (g : Graph) : Decidable (HasNT g) := by unfold HasNT; infer_instance
instance (g : Graph) : Decidable (HasIsolatedNT g) := by unfold HasIsolatedNT; infer_instance

section
variable {g h : Graph} {σ τ : Nat → Nat}
  (hσ : ∀ x, x < 10 → σ x < 10 ∧ τ (σ x) = x)
  (hτ : ∀ y, y < 10 → τ y < 10 ∧ σ (τ y) = y)
  (hgh : ∀ u, u < 10 → ∀ v, v < 10 → g u v = h (σ u) (σ v))
include hσ hτ hgh

omit hσ in
theorem nt_map {u v : Nat} (hu : u < 10) (hv : v < 10) : NT g u v → NT h (σ u) (σ v) := by
  rintro ⟨huv, hno⟩
  refine ⟨by rw [← hgh u hu v hv]; exact huv, fun w hw ⟨h1, h2⟩ => hno (τ w) (hτ w hw).1 ⟨?_, ?_⟩⟩
  · rw [hgh u hu (τ w) (hτ w hw).1, (hτ w hw).2]; exact h1
  · rw [hgh v hv (τ w) (hτ w hw).1, (hτ w hw).2]; exact h2

omit hτ in
theorem nt_unmap {u v : Nat} (hu : u < 10) (hv : v < 10) : NT h (σ u) (σ v) → NT g u v := by
  rintro ⟨huv, hno⟩
  refine ⟨by rw [hgh u hu v hv]; exact huv, fun w hw ⟨h1, h2⟩ => hno (σ w) (hσ w hw).1 ⟨?_, ?_⟩⟩
  · rw [← hgh u hu w hw]; exact h1
  · rw [← hgh v hv w hw]; exact h2

theorem hasNT_map : HasNT g → HasNT h := by
  rintro ⟨u, hu, v, hv, hnt⟩
  exact ⟨σ u, (hσ u hu).1, σ v, (hσ v hv).1, nt_map hτ hgh hu hv hnt⟩

theorem hasIsolatedNT_map : HasIsolatedNT g → HasIsolatedNT h := by
  rintro ⟨u, hu, v, hv, hnt, hiso⟩
  refine ⟨σ u, (hσ u hu).1, σ v, (hσ v hv).1, nt_map hτ hgh hu hv hnt, fun w hw => ⟨?_, ?_⟩⟩
  · intro hne hw'
    have hw1 := (hτ w hw).1
    have hback : NT g u (τ w) := nt_unmap hσ hgh hu hw1 (by rw [(hτ w hw).2]; exact hw')
    refine (hiso (τ w) hw1).1 ?_ hback
    intro heq; apply hne; rw [← (hτ w hw).2, heq]
  · intro hne hw'
    have hw1 := (hτ w hw).1
    have hback : NT g v (τ w) := nt_unmap hσ hgh hv hw1 (by rw [(hτ w hw).2]; exact hw')
    refine (hiso (τ w) hw1).2 ?_ hback
    intro heq; apply hne; rw [← (hτ w hw).2, heq]
end

theorem iso_hasNT {g h : Graph} (hi : Iso g h) : HasNT g → HasNT h := by
  obtain ⟨σ, τ, hσ, hτ, hgh⟩ := hi; exact hasNT_map hσ hτ hgh

theorem iso_hasIsolatedNT {g h : Graph} (hi : Iso g h) : HasIsolatedNT g → HasIsolatedNT h := by
  obtain ⟨σ, τ, hσ, hτ, hgh⟩ := hi; exact hasIsolatedNT_map hσ hτ hgh

/-! ## Facts about the four graphs -/

theorem simple_all : IsSimple A1 ∧ IsSimple B1 ∧ IsSimple A2 ∧ IsSimple B2 := by decide
theorem regular_all : Regular A1 4 ∧ Regular B1 4 ∧ Regular A2 4 ∧ Regular B2 4 := by decide
theorem cospectral_1 : Cospectral A1 B1 := by decide
theorem cospectral_2 : Cospectral A2 B2 := by decide
/-- The two pairs have different spectra (6 closed walks of length 3 differ). -/
theorem spectra_differ : closedWalks A1 3 ≠ closedWalks A2 3 := by decide

theorem invariants :
    ¬ HasNT A1 ∧ HasNT B1 ∧ HasNT A2 ∧ HasNT B2 ∧
    HasIsolatedNT A2 ∧ ¬ HasIsolatedNT B2 := by decide

theorem not_iso_A1_B1 : ¬ Iso A1 B1 := fun hi => invariants.1 (iso_hasNT (iso_symm hi) invariants.2.1)
theorem not_iso_A2_B2 : ¬ Iso A2 B2 := fun hi => invariants.2.2.2.2.2 (iso_hasIsolatedNT hi invariants.2.2.2.2.1)
theorem not_iso_A1_A2 : ¬ Iso A1 A2 := fun hi => invariants.1 (iso_hasNT (iso_symm hi) invariants.2.2.1)
theorem not_iso_A1_B2 : ¬ Iso A1 B2 := fun hi => invariants.1 (iso_hasNT (iso_symm hi) invariants.2.2.2.1)

/-! ## The uniqueness clause and its refutation -/

/-- A cospectral regular pair of order 10: two simple regular graphs on
10 vertices with the same spectrum that are not isomorphic. -/
def CospectralRegularPair (g h : Graph) : Prop :=
  IsSimple g ∧ IsSimple h ∧ (∃ k, Regular g k) ∧ (∃ k, Regular h k) ∧
    Cospectral g h ∧ ¬ Iso g h

/-- "The cospectral regular pair of order 10 is unique" (up to isomorphism,
as an unordered pair). -/
def UniquePair : Prop :=
  ∀ g h g' h', CospectralRegularPair g h → CospectralRegularPair g' h' →
    (Iso g g' ∧ Iso h h') ∨ (Iso g h' ∧ Iso h g')

theorem pair_1 : CospectralRegularPair A1 B1 :=
  ⟨simple_all.1, simple_all.2.1, ⟨4, regular_all.1⟩, ⟨4, regular_all.2.1⟩, cospectral_1,
    not_iso_A1_B1⟩

theorem pair_2 : CospectralRegularPair A2 B2 :=
  ⟨simple_all.2.2.1, simple_all.2.2.2, ⟨4, regular_all.2.2.1⟩, ⟨4, regular_all.2.2.2⟩,
    cospectral_2, not_iso_A2_B2⟩

theorem conjecture_00000002141_false : ¬ UniquePair := by
  intro h
  rcases h A1 B1 A2 B2 pair_1 pair_2 with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact not_iso_A1_A2 h1
  · exact not_iso_A1_B2 h1

end Cospectral

#print axioms Cospectral.cospectral_1
#print axioms Cospectral.invariants
#print axioms Cospectral.pair_1
#print axioms Cospectral.pair_2
#print axioms Cospectral.conjecture_00000002141_false
