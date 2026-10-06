import Mathlib

/-!
# Conjecture 00000002149 (disproof)

Claim: for every finite graph `G`, `μ(Ḡ) ≤ |V| − ω(G) − 1`, where `μ` is the Colin de Verdière
parameter and `ω` the clique number, with equality for complete graphs (whose complement has
no edges).

We formalise `μ(G)` as the largest corank of a real symmetric matrix `M` with
(M1) `M i j < 0` for adjacent `i ≠ j` and `M i j = 0` for non-adjacent `i ≠ j`,
(M2) exactly one negative eigenvalue (counted with multiplicity),
(M3) the Strong Arnold Hypothesis: the only symmetric `X` with `X i i = 0`, `X i j = 0` on edges
and `M X = 0` is `X = 0`.

Two families of counterexamples:
* `G = K_n` (`n ≥ 1`), the case the conjecture names as tight: the bound is `−1`, but the
  edgeless complement has an admissible matrix (of corank `1` when `n ≥ 2`);
* `G` edgeless on `n ≥ 2` vertices: the bound is `n − 2`, but `μ(K_n) ≥ n − 1`
  (witness `M = −J`).
-/

open Matrix Polynomial Finset

namespace C2149

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Colin de Verdière conditions (M1)–(M3) on a real matrix `M` for the graph `G`. -/
structure IsCdVMatrix (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop where
  symm : M.IsHermitian
  adj : ∀ i j, i ≠ j → G.Adj i j → M i j < 0
  nonadj : ∀ i j, i ≠ j → ¬ G.Adj i j → M i j = 0
  one_neg : (univ.filter fun i => symm.eigenvalues i < 0).card = 1
  sah : ∀ X : Matrix V V ℝ, X.IsSymm → (∀ i, X i i = 0) → (∀ i j, G.Adj i j → X i j = 0) →
    M * X = 0 → X = 0

/-- The corank `|V| − rank M`. -/
noncomputable def corank (M : Matrix V V ℝ) : ℕ := Fintype.card V - M.rank

/-- The Colin de Verdière parameter: the largest corank of a matrix satisfying (M1)–(M3). -/
noncomputable def cdvMu (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ M, IsCdVMatrix G M ∧ corank M = k}

lemma le_cdvMu {G : SimpleGraph V} {M : Matrix V V ℝ} (h : IsCdVMatrix G M) :
    corank M ≤ cdvMu G :=
  le_csSup ⟨Fintype.card V, by rintro _ ⟨M, -, rfl⟩; exact Nat.sub_le _ _⟩ ⟨M, h, rfl⟩

/-- The eigenvalues of a diagonal matrix are its diagonal entries (as a multiset), so the
number of negative eigenvalues is the number of negative diagonal entries. -/
lemma card_neg_eig_diagonal (d : V → ℝ) (h : (diagonal d).IsHermitian) :
    (univ.filter fun i => h.eigenvalues i < 0).card = (univ.filter fun i => d i < 0).card := by
  have hr := h.roots_charpoly_eq_eigenvalues
  rw [charpoly_diagonal] at hr
  have h2 : (∏ i, (X - C (d i)) : ℝ[X]) = ((univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h2, roots_multiset_prod_X_sub_C] at hr
  have h3 := congrArg (fun s : Multiset ℝ => (s.filter (· < 0)).card) hr
  simp only [Multiset.filter_map, Multiset.card_map] at h3
  exact h3.symm

/-! ### Complete graphs (the case named as tight) -/

lemma cliqueNum_top (n : ℕ) : (⊤ : SimpleGraph (Fin n)).cliqueNum = n := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (⊤ : SimpleGraph (Fin n)).exists_isNClique_cliqueNum
    rw [← hs.card_eq]
    simpa using card_le_univ s
  · have hc : (⊤ : SimpleGraph (Fin n)).IsClique (univ : Finset (Fin n)) := by
      intro x _ y _ hxy; exact (SimpleGraph.top_adj x y).mpr hxy
    simpa using hc.card_le_cliqueNum

/-- Diagonal witness `diag(−1, 0, 1, …, 1)` for the edgeless graph. -/
noncomputable def dEmpty (n : ℕ) : Fin n → ℝ :=
  fun i => if i.val = 0 then -1 else if i.val = 1 then 0 else 1

lemma dEmpty_ne_zero {n : ℕ} {i : Fin n} (h : i.val ≠ 1) : dEmpty n i ≠ 0 := by
  unfold dEmpty; split_ifs <;> norm_num

theorem isCdV_empty (n : ℕ) (hn : 1 ≤ n) :
    IsCdVMatrix (⊤ : SimpleGraph (Fin n))ᶜ (diagonal (dEmpty n)) where
  symm := isHermitian_diagonal _
  adj i j _ h := by simp at h
  nonadj i j hij _ := diagonal_apply_ne _ hij
  one_neg := by
    rw [card_neg_eig_diagonal]
    have : (univ.filter fun i : Fin n => dEmpty n i < 0) = {⟨0, hn⟩} := by
      ext i
      rw [Finset.mem_filter]
      by_cases h0 : i.val = 0 <;> by_cases h1 : i.val = 1 <;> simp [dEmpty, Fin.ext_iff, h0, h1]
    rw [this, card_singleton]
  sah X hX hd _ hMX := by
    have row : ∀ i j, i.val ≠ 1 → X i j = 0 := fun i j hi => by
      have := congrFun (congrFun hMX i) j
      rw [diagonal_mul] at this
      simpa [dEmpty_ne_zero hi] using this
    ext i j
    by_cases hi : i.val = 1
    · by_cases hj : j.val = 1
      · have : i = j := Fin.ext (hi.trans hj.symm)
        subst this; simpa using hd i
      · rw [← hX.apply i j]; simpa using row j i hj
    · simpa using row i j hi

lemma corank_empty (n : ℕ) (hn : 2 ≤ n) : corank (diagonal (dEmpty n)) = 1 := by
  unfold corank
  rw [rank_diagonal, Fintype.card_subtype, Fintype.card_fin]
  have : (univ.filter fun i : Fin n => dEmpty n i ≠ 0) = univ.erase ⟨1, by omega⟩ := by
    ext i
    rw [Finset.mem_filter]
    by_cases h0 : i.val = 0 <;> by_cases h1 : i.val = 1 <;> simp [dEmpty, Fin.ext_iff, h0, h1]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/-! ### Edgeless graphs: complement `K_n`, witness `−J` -/

lemma cliqueNum_bot (n : ℕ) (hn : 1 ≤ n) : (⊥ : SimpleGraph (Fin n)).cliqueNum = 1 := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (⊥ : SimpleGraph (Fin n)).exists_isNClique_cliqueNum
    rw [← hs.card_eq]
    exact card_le_one.mpr fun a ha b hb => by
      by_contra hab; exact (hs.isClique ha hb hab).elim
  · have hc : (⊥ : SimpleGraph (Fin n)).IsClique ({⟨0, hn⟩} : Finset (Fin n)) := by simp
    simpa using hc.card_le_cliqueNum

/-- The all-`(−1)` matrix `−J`. -/
def negJ (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := of fun _ _ => -1

lemma negJ_herm (n : ℕ) : (negJ n).IsHermitian := by
  ext i j; simp [negJ, conjTranspose_apply]

lemma negJ_sq (n : ℕ) : negJ n * negJ n = (-(n : ℝ)) • negJ n := by
  ext i j; simp [negJ, mul_apply]

/-- Every eigenvalue of `−J` is `0` or `−n`. -/
lemma negJ_eig (n : ℕ) (i : Fin n) :
    (negJ_herm n).eigenvalues i = 0 ∨ (negJ_herm n).eigenvalues i = -n := by
  set h := negJ_herm n
  set v := ⇑(h.eigenvectorBasis i)
  set l := h.eigenvalues i
  have hv : negJ n *ᵥ v = l • v := h.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := by
    intro h0
    have := (h.eigenvectorBasis).orthonormal.1 i
    rw [show h.eigenvectorBasis i = 0 from by ext k; exact congrFun h0 k] at this
    simp at this
  have key : (l * l + n * l) • v = 0 := by
    have e1 : negJ n *ᵥ (negJ n *ᵥ v) = (l * l) • v := by
      rw [hv, mulVec_smul, hv, smul_smul]
    have e2 : negJ n *ᵥ (negJ n *ᵥ v) = (-(n : ℝ) * l) • v := by
      rw [mulVec_mulVec, negJ_sq, smul_mulVec, hv, smul_smul]
    rw [add_smul, e1.symm, show (n * l : ℝ) = -(-(n : ℝ) * l) by ring, neg_smul, ← e2, add_neg_cancel]
  rcases smul_eq_zero.mp key with h1 | h1
  · have : l * (l + n) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by linarith)
  · exact absurd h1 hv0

/-- Exactly one eigenvalue of `−J` equals `−n` (`n ≥ 1`). -/
lemma negJ_card (n : ℕ) (hn : 1 ≤ n) :
    (univ.filter fun i => (negJ_herm n).eigenvalues i = -n).card = 1 := by
  set h := negJ_herm n
  have htr := h.trace_eq_sum_eigenvalues
  have ht : (negJ n).trace = -n := by simp [negJ, trace]
  have hsum : ∑ i, h.eigenvalues i = ∑ i ∈ univ.filter (fun i => h.eigenvalues i = -n), (-n : ℝ) := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rcases negJ_eig n i with h0 | h0 <;> simp [h0]
  rw [ht] at htr
  simp only [RCLike.ofReal_real_eq_id, id] at htr
  rw [hsum, sum_const, nsmul_eq_mul] at htr
  have hn' : (n : ℝ) ≠ 0 := by norm_cast; omega
  have : ((univ.filter fun i => h.eigenvalues i = -n).card : ℝ) = 1 := by
    field_simp at htr; linarith
  exact_mod_cast this

lemma negJ_filter_eq (n : ℕ) (hn : 1 ≤ n) (p : ℝ → Prop) [DecidablePred p] (hp0 : ¬ p 0)
    (hpn : p (-n)) : (univ.filter fun i => p ((negJ_herm n).eigenvalues i)) =
      univ.filter fun i => (negJ_herm n).eigenvalues i = -n := by
  ext i
  simp only [mem_filter, mem_univ, true_and]
  rcases negJ_eig n i with h0 | h0
  · rw [h0]
    have : (0 : ℝ) ≠ -n := by
      intro h; have : (n : ℝ) = 0 := by linarith
      norm_cast at this; omega
    simp [hp0, this]
  · simp [h0, hpn]

theorem isCdV_complete (n : ℕ) (hn : 1 ≤ n) :
    IsCdVMatrix (⊥ : SimpleGraph (Fin n))ᶜ (negJ n) where
  symm := negJ_herm n
  adj i j _ _ := by simp [negJ]
  nonadj i j hij h := by simp [hij] at h
  one_neg := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [negJ_filter_eq n hn (· < 0) (lt_irrefl 0) (by simpa using hn'), negJ_card n hn]
  sah X _ hd hE _ := by
    ext i j
    by_cases hij : i = j
    · subst hij; simpa using hd i
    · simpa using hE i j (by simpa using hij)

lemma corank_negJ (n : ℕ) (hn : 1 ≤ n) : corank (negJ n) = n - 1 := by
  unfold corank
  rw [(negJ_herm n).rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    negJ_filter_eq n hn (· ≠ 0) (by simp) (by simp; omega), negJ_card n hn, Fintype.card_fin]

/-- **Main theorem.** The inequality `μ(Ḡ) ≤ |V| − ω(G) − 1` fails
(a) for every complete graph `G = K_n`, `n ≥ 1` (the case named as tight): the complement has an
admissible matrix, so `μ(Ḡ) ≥ 0 > −1`; for `n ≥ 2` that matrix has corank `1`, so `μ(Ḡ) ≥ 1`;
(b) for every edgeless graph `G` on `n ≥ 2` vertices: `ω(G) = 1` and `μ(Ḡ) = μ(K_n) ≥ n − 1`,
which exceeds `n − 2`. -/
theorem conjecture_2149_false :
    (∀ n : ℕ, 1 ≤ n → ∃ M, IsCdVMatrix (⊤ : SimpleGraph (Fin n))ᶜ M ∧
      ((n : ℤ) - (⊤ : SimpleGraph (Fin n)).cliqueNum - 1 < corank M) ∧
      (2 ≤ n → corank M = 1 ∧ 1 ≤ cdvMu (⊤ : SimpleGraph (Fin n))ᶜ) ∧
      ¬ ((cdvMu (⊤ : SimpleGraph (Fin n))ᶜ : ℤ) ≤ n - (⊤ : SimpleGraph (Fin n)).cliqueNum - 1)) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ M, IsCdVMatrix (⊥ : SimpleGraph (Fin n))ᶜ M ∧ corank M = n - 1 ∧
      (⊥ : SimpleGraph (Fin n)).cliqueNum = 1 ∧
      ¬ ((cdvMu (⊥ : SimpleGraph (Fin n))ᶜ : ℤ) ≤ n - (⊥ : SimpleGraph (Fin n)).cliqueNum - 1)) := by
  refine ⟨fun n hn => ⟨_, isCdV_empty n hn, ?_, fun h2 => ⟨corank_empty n h2,
    corank_empty n h2 ▸ le_cdvMu (isCdV_empty n hn)⟩, ?_⟩,
    fun n hn => ⟨_, isCdV_complete n (by omega), corank_negJ n (by omega), cliqueNum_bot n (by omega),
      ?_⟩⟩
  · rw [cliqueNum_top]; omega
  · rw [cliqueNum_top]; omega
  · have := le_cdvMu (isCdV_complete n (by omega))
    rw [corank_negJ n (by omega)] at this
    rw [cliqueNum_bot n (by omega)]
    omega

end C2149
