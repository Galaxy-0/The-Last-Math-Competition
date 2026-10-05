import Mathlib

/-!
# Conjecture 00000002167 is false

The conjecture: among `n`-vertex graphs of girth `≥ 5`, the maximum spectral radius is attained by
"Moore-approximate" graphs, and the extremal graphs are unique (for every `n ≥ 5`).

We refute the uniqueness clause at `n = 5`:

* every graph `G` of girth `≥ 5` on `n` vertices has spectral radius `≤ √(n - 1)`
  (`spectralRadius_le_sqrt`), because in such a graph `∑_{l ~ i} deg l ≤ n - 1` for every vertex `i`;
* the 5-cycle `C₅` (Mathlib's `cycleGraph 5`) and the star `K_{1,4}` both have girth `≥ 5` and
  spectral radius exactly `2 = √(5 - 1)`;
* they are not isomorphic (5 edges versus 4).

So for `n = 5` there are two non-isomorphic extremal graphs, both connected.

Definitions used: girth is Mathlib's `SimpleGraph.egirth` (length of a shortest cycle, `⊤` for a
forest), and the spectral radius is Mathlib's `spectralRadius ℂ` of the complex adjacency matrix,
i.e. `sup {‖λ‖ : λ ∈ spectrum}`.
-/

open SimpleGraph Matrix

namespace C2167

variable {V : Type*}

/-! ### Spectral radius and girth -/

/-- The spectral radius of a finite graph: `sup ‖λ‖` over the (complex) spectrum of its adjacency
matrix, using Mathlib's `spectralRadius`. -/
noncomputable def adjSpectralRadius [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ENNReal := by
  classical exact spectralRadius ℂ (G.adjMatrix ℂ)

lemma adjSpectralRadius_eq [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjSpectralRadius G = spectralRadius ℂ (G.adjMatrix ℂ) := by
  unfold adjSpectralRadius
  congr!

/-- A graph of girth `≥ 5` has no triangle. -/
lemma no_triangle {G : SimpleGraph V} (hG : 5 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hw : w.IsCycle := by
    rw [Walk.cons_isCycle_iff, Walk.isPath_def]
    simp [hab.ne, hbc.ne, hca.ne, hab.ne.symm, hca.ne.symm]
  have h : (5 : ℕ∞) ≤ 3 := by simpa [w] using hG.trans (G.egirth_le_length hw)
  have : (5 : ℕ) ≤ 3 := by exact_mod_cast h
  omega

/-- A graph of girth `≥ 5` has no 4-cycle. -/
lemma no_quad {G : SimpleGraph V} (hG : 5 ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hw : w.IsCycle := by
    rw [Walk.cons_isCycle_iff, Walk.isPath_def]
    simp [hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hda.ne.symm, hac, hbd, hac.symm]
  have h : (5 : ℕ∞) ≤ 4 := by simpa [w] using hG.trans (G.egirth_le_length hw)
  have : (5 : ℕ) ≤ 4 := by exact_mod_cast h
  omega

/-- Conversely, no triangle and no 4-cycle give girth `≥ 5`. -/
lemma five_le_egirth {G : SimpleGraph V}
    (h3 : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False) :
    5 ≤ G.egirth := by
  rw [le_egirth]
  intro a w hw
  have h3le : 3 ≤ w.length := hw.three_le_length
  by_contra hlt
  have hlen : w.length < 5 := by
    by_contra h; exact hlt (by exact_mod_cast (not_lt.mp h))
  have hnd := hw.support_nodup
  cases w with
  | nil => simp at h3le
  | cons hab w =>
    cases w with
    | nil => simp at h3le
    | cons hbc w =>
      cases w with
      | nil => simp at h3le
      | cons hcx w =>
        cases w with
        | nil => exact h3 _ _ _ hab hbc hcx
        | cons hcd w =>
          cases w with
          | nil =>
            simp at hnd
            exact h4 _ _ _ _ hab hbc hcx hcd (by tauto) (by tauto)
          | cons _ w => simp at hlen; omega

/-! ### The bound `λ ≤ √(n - 1)` for girth `≥ 5` -/

variable [Fintype V] [DecidableEq V]

/-- In a graph of girth `≥ 5`, `∑_{l ~ i} deg l ≤ n - 1`: the sets `N(l) \ {i}` (`l ~ i`) are
pairwise disjoint (no 4-cycle) and avoid `{i} ∪ N(i)` (no triangle). -/
lemma sum_degree_neighbors_le {G : SimpleGraph V} [DecidableRel G.Adj] (hG : 5 ≤ G.egirth)
    (i : V) : ∑ l ∈ G.neighborFinset i, G.degree l ≤ Fintype.card V - 1 := by
  set S := G.neighborFinset i
  let T : V → Finset V := fun l => (G.neighborFinset l).erase i
  have hdisj : (S : Set V).PairwiseDisjoint T := by
    intro l hl l' hl' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [T, Finset.mem_erase, mem_neighborFinset] at hj hj'
    simp only [S, Finset.mem_coe, mem_neighborFinset] at hl hl'
    exact no_quad hG hl hj.2 hj'.2.symm hl'.symm (Ne.symm hj.1) hne
  have hsub : S.biUnion T ⊆ Finset.univ \ insert i S := by
    intro j hj
    simp only [Finset.mem_biUnion, T, Finset.mem_erase, mem_neighborFinset] at hj
    obtain ⟨l, hl, hji, hlj⟩ := hj
    simp only [S, mem_neighborFinset] at hl
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, S, mem_neighborFinset,
      true_and, not_or]
    exact ⟨hji, fun hij => no_triangle hG hl hlj hij.symm⟩
  have hsum : ∑ l ∈ S, G.degree l = ∑ l ∈ S, ((T l).card + 1) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [S, mem_neighborFinset] at hl
    rw [Finset.card_erase_add_one (by simpa using hl.symm), card_neighborFinset_eq_degree]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_insert_of_notMem (by simp [S]), Finset.card_univ,
    Finset.card_biUnion hdisj] at hcard
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  have : S.card + 1 ≤ Fintype.card V := by
    have := Finset.card_le_univ (insert i S)
    rwa [Finset.card_insert_of_notMem (by simp [S])] at this
  omega

/-- An element of the spectrum of a complex matrix has an eigenvector. -/
lemma exists_eigenvector {A : Matrix V V ℂ} {k : ℂ} (hk : k ∈ spectrum ℂ A) :
    ∃ v : V → ℂ, v ≠ 0 ∧ A *ᵥ v = k • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff] at hk
  obtain ⟨v, hv, h⟩ := hk
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h, Matrix.algebraMap_eq_diagonal]
  ext j
  simp [Matrix.mulVec_diagonal]

/-- An eigenvalue (with a nonzero eigenvector) lies in the spectrum. -/
lemma mem_spectrum_of_eigenvector {A : Matrix V V ℂ} {k : ℂ} {v : V → ℂ} (hv : v ≠ 0)
    (h : A *ᵥ v = k • v) : k ∈ spectrum ℂ A := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.algebraMap_eq_diagonal, sub_eq_zero]
  ext j
  simp [Matrix.mulVec_diagonal]

/-- Every adjacency eigenvalue `λ` of a graph of girth `≥ 5` on `n` vertices has `|λ|² ≤ n - 1`. -/
lemma norm_sq_le_of_mem_spectrum {G : SimpleGraph V} [DecidableRel G.Adj] (hG : 5 ≤ G.egirth)
    {k : ℂ} (hk : k ∈ spectrum ℂ (G.adjMatrix ℂ)) : ‖k‖ ^ 2 ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by
  obtain ⟨v, hv, hAv⟩ := exists_eigenvector hk
  have hne : Nonempty V := by
    by_contra h
    exact hv (funext fun j => ((not_nonempty_iff.mp h).false j).elim)
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ‖v j‖)
  have hvi : 0 < ‖v i‖ := by
    by_contra h
    exact hv (funext fun j => norm_le_zero_iff.mp ((hi j).trans (not_lt.mp h)))
  have h1 : ∀ l, ∑ j ∈ G.neighborFinset l, v j = k * v l := fun l => by
    rw [← adjMatrix_mulVec_apply, hAv]
    simp
  have key : k ^ 2 * v i = ∑ l ∈ G.neighborFinset i, ∑ j ∈ G.neighborFinset l, v j := by
    simp_rw [h1, ← Finset.mul_sum, h1]
    ring
  have bound : ‖k‖ ^ 2 * ‖v i‖ ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * ‖v i‖ := by
    calc ‖k‖ ^ 2 * ‖v i‖ = ‖k ^ 2 * v i‖ := by rw [norm_mul, norm_pow]
      _ = ‖∑ l ∈ G.neighborFinset i, ∑ j ∈ G.neighborFinset l, v j‖ := by rw [key]
      _ ≤ ∑ l ∈ G.neighborFinset i, ∑ j ∈ G.neighborFinset l, ‖v j‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
      _ ≤ ∑ l ∈ G.neighborFinset i, ∑ j ∈ G.neighborFinset l, ‖v i‖ :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hi j
      _ = ((∑ l ∈ G.neighborFinset i, G.degree l : ℕ) : ℝ) * ‖v i‖ := by
          simp [Finset.sum_mul, card_neighborFinset_eq_degree]
      _ ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * ‖v i‖ := by
          gcongr
          exact sum_degree_neighbors_le hG i
  exact le_of_mul_le_mul_right bound hvi

/-- **Spectral bound.** A graph of girth `≥ 5` on `n` vertices has spectral radius `≤ √(n - 1)`. -/
theorem spectralRadius_le_sqrt (G : SimpleGraph V) (hG : 5 ≤ G.egirth) :
    adjSpectralRadius G ≤ ENNReal.ofReal (Real.sqrt ((Fintype.card V - 1 : ℕ) : ℝ)) := by
  classical
  rw [adjSpectralRadius_eq, spectralRadius]
  refine iSup₂_le fun k hk => ?_
  have h := norm_sq_le_of_mem_spectrum hG hk
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le h)

/-! ### The two extremal graphs on 5 vertices -/

/-- The star `K_{1,n}` on `Fin (n + 1)`, with centre `0`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (starGraph n).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i = 0 ∨ j = 0)))

lemma egirth_cycleGraph_five : 5 ≤ (cycleGraph 5).egirth :=
  five_le_egirth (by decide) (by decide)

lemma egirth_star_four : 5 ≤ (starGraph 4).egirth :=
  five_le_egirth (by decide) (by decide)

lemma two_mem_spectrum_cycle : (2 : ℂ) ∈ spectrum ℂ ((cycleGraph 5).adjMatrix ℂ) := by
  refine mem_spectrum_of_eigenvector (v := fun _ => 1) (fun h => by simpa using congrFun h 0) ?_
  ext i
  rw [adjMatrix_mulVec_apply]
  simp only [Finset.sum_const, card_neighborFinset_eq_degree, Pi.smul_apply, smul_eq_mul, mul_one]
  have hd : (cycleGraph 5).degree i = 2 := cycleGraph_degree_three_le (n := 2)
  rw [hd]
  norm_num

lemma two_mem_spectrum_star : (2 : ℂ) ∈ spectrum ℂ ((starGraph 4).adjMatrix ℂ) := by
  refine mem_spectrum_of_eigenvector (v := ![2, 1, 1, 1, 1])
    (fun h => by simpa using congrFun h 1) ?_
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, adjMatrix_apply] <;>
    simp [starGraph, Fin.sum_univ_succ]
  norm_num

lemma le_adjSpectralRadius_of_mem {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℂ}
    (hk : k ∈ spectrum ℂ (G.adjMatrix ℂ)) : (‖k‖₊ : ENNReal) ≤ adjSpectralRadius G := by
  rw [adjSpectralRadius_eq, spectralRadius]
  exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (G.adjMatrix ℂ)) => (‖k‖₊ : ENNReal)) k hk

lemma bound_five (G : SimpleGraph (Fin 5)) (hG : 5 ≤ G.egirth) : adjSpectralRadius G ≤ 2 := by
  refine (spectralRadius_le_sqrt G hG).trans (le_of_eq ?_)
  have : Real.sqrt (((Fintype.card (Fin 5) - 1 : ℕ) : ℝ)) = 2 := by
    rw [Fintype.card_fin, show ((5 - 1 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]
  simp

lemma spec_two_of_mem {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj] (hG : 5 ≤ G.egirth)
    (hk : (2 : ℂ) ∈ spectrum ℂ (G.adjMatrix ℂ)) : adjSpectralRadius G = 2 := by
  refine le_antisymm (bound_five G hG) ?_
  have := le_adjSpectralRadius_of_mem hk
  have h2 : ‖(2 : ℂ)‖₊ = 2 := by
    rw [← NNReal.coe_inj]
    simp
  rwa [h2] at this

/-! ### The conjecture -/

/-- `G` attains the maximum spectral radius among graphs of girth `≥ 5` on `Fin n` that satisfy the
side condition `P` (`P = fun _ => True` for all graphs, `Connected` for connected graphs). -/
def IsSpecExtremal {n : ℕ} (P : SimpleGraph (Fin n) → Prop) (G : SimpleGraph (Fin n)) : Prop :=
  5 ≤ G.egirth ∧ P G ∧
    ∀ H : SimpleGraph (Fin n), 5 ≤ H.egirth → P H → adjSpectralRadius H ≤ adjSpectralRadius G

/-- The uniqueness clause: the extremal graph on `n` vertices is unique up to isomorphism. -/
def UniqueExtremal (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ G H : SimpleGraph (Fin n), IsSpecExtremal P G → IsSpecExtremal P H → Nonempty (G ≃g H)

lemma star_connected : (starGraph 4).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun j => ?_⟩
  by_cases hj : j = 0
  · rw [hj]
  · exact Adj.reachable ⟨Ne.symm hj, Or.inl rfl⟩

lemma not_iso : IsEmpty (cycleGraph 5 ≃g starGraph 4) := by
  refine ⟨fun f => ?_⟩
  have h := f.card_edgeFinset_eq
  have h1 : (cycleGraph 5).edgeFinset.card = 5 := by decide
  have h2 : (starGraph 4).edgeFinset.card = 4 := by decide
  omega

/-- **Main theorem.** On 5 vertices, `C₅` and `K_{1,4}` both have girth `≥ 5`, are connected, and
have spectral radius `2`, which is the maximum over all graphs of girth `≥ 5` on 5 vertices; yet
they are not isomorphic. -/
theorem main :
    adjSpectralRadius (cycleGraph 5) = 2 ∧ adjSpectralRadius (starGraph 4) = 2 ∧
      (∀ G : SimpleGraph (Fin 5), 5 ≤ G.egirth → adjSpectralRadius G ≤ 2) ∧
      IsSpecExtremal (fun _ => True) (cycleGraph 5) ∧ IsSpecExtremal (fun _ => True) (starGraph 4) ∧
      IsSpecExtremal Connected (cycleGraph 5) ∧ IsSpecExtremal Connected (starGraph 4) ∧
      IsEmpty (cycleGraph 5 ≃g starGraph 4) := by
  have hC := spec_two_of_mem egirth_cycleGraph_five two_mem_spectrum_cycle
  have hS := spec_two_of_mem egirth_star_four two_mem_spectrum_star
  have hCc : (cycleGraph 5).Connected := cycleGraph_connected
  refine ⟨hC, hS, bound_five, ⟨egirth_cycleGraph_five, trivial, fun H hH _ => ?_⟩,
    ⟨egirth_star_four, trivial, fun H hH _ => ?_⟩, ⟨egirth_cycleGraph_five, hCc, fun H hH _ => ?_⟩,
    ⟨egirth_star_four, star_connected, fun H hH _ => ?_⟩, not_iso⟩ <;>
    first | (rw [hC]; exact bound_five H hH) | (rw [hS]; exact bound_five H hH)

/-- **The conjecture is false.** Uniqueness of the spectral-radius maximizer among graphs of girth
`≥ 5` fails at `n = 5`, both among all graphs and among connected graphs. -/
theorem conjecture_false :
    ¬ (∀ n, 5 ≤ n → UniqueExtremal n (fun _ => True)) ∧
      ¬ (∀ n, 5 ≤ n → UniqueExtremal n Connected) := by
  obtain ⟨-, -, -, h1, h2, h3, h4, hiso⟩ := main
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨f⟩ := h 5 le_rfl _ _ h1 h2
    exact hiso.false f
  · obtain ⟨f⟩ := h 5 le_rfl _ _ h3 h4
    exact hiso.false f

end C2167
