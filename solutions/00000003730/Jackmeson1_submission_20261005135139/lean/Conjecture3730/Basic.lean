import Mathlib

/-!
# Conjecture 00000003730 (disproof)

Claim: for the graph energy `E(G) = Σ |λᵢ|` (sum of absolute values of the eigenvalues of the
adjacency matrix), (i) the maximum energy is attained by complete bipartite graphs, and
(ii) among trees the minimum energy is attained by paths.

We refute both parts:
* (i) for every `n ≥ 3`, the complete graph `K_n` has energy `2(n-1)`, while every complete
  bipartite graph `K_{a,b}` with `a + b = n` has energy `2√(ab) ≤ n < 2(n-1)`;
* (ii) on `4` vertices the star `K_{1,3}` is a tree of energy `2√3`, while the path `P_4` has
  energy `2√5 > 2√3`.
-/

namespace C3730

open Matrix SimpleGraph Finset

/-! ## Energy -/

/-- The energy of a finite simple graph: the sum of the absolute values of the (real)
eigenvalues of its adjacency matrix, as given by Mathlib's spectral theorem. -/
noncomputable def energy {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  ∑ i, |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues i|

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Eigenvector equation with a nonzero eigenvector. -/
lemma exists_eigvec {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : V) :
    ∃ v : V → ℝ, v ≠ 0 ∧ A *ᵥ v = hA.eigenvalues i • v := by
  refine ⟨⇑(hA.eigenvectorBasis i), ?_, hA.mulVec_eigenvectorBasis i⟩
  intro h
  apply hA.eigenvectorBasis.orthonormal.ne_zero i
  ext j
  simpa using congrFun h j

/-- Sum of eigenvalues = trace. -/
lemma sum_eig {A : Matrix V V ℝ} (hA : A.IsHermitian) : ∑ i, hA.eigenvalues i = A.trace := by
  rw [hA.trace_eq_sum_eigenvalues]; simp

/-- Sum of squared eigenvalues = trace of `A * A` (from the spectral theorem). -/
lemma sum_eig_sq {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues i ^ 2 = (A * A).trace := by
  have h := hA.spectral_theorem
  set U := hA.eigenvectorUnitary
  set D : Matrix V V ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAA : A * A = (U : Matrix V V ℝ) * (D * D) * star (U : Matrix V V ℝ) := by
    conv_lhs => rw [h]
    rw [← map_mul, Unitary.conjStarAlgAut_apply]
  rw [hAA, trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  simp [D, diagonal_mul_diagonal, trace_diagonal, sq]

omit [DecidableEq V] in
lemma trace_sq_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ * G.adjMatrix ℝ).trace = 2 * #G.edgeFinset := by
  simp only [trace, Matrix.diag, adjMatrix_mul_self_apply_self]
  rw [← Nat.cast_sum, sum_degrees_eq_twice_card_edges]; push_cast; ring

/-- Energy via a pointwise formula `|λ| = f λ` valid on every eigenvalue. -/
lemma energy_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℝ → ℝ)
    (hf : ∀ i, |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues i| =
      f ((G.isHermitian_adjMatrix (R := ℝ)).eigenvalues i)) :
    energy G = ∑ i, f ((G.isHermitian_adjMatrix (R := ℝ)).eigenvalues i) := by
  unfold energy; exact Finset.sum_congr rfl (fun i _ => hf i)

end General

/-! ## Complete graphs: `E(K_n) = 2(n-1)` -/

lemma eig_top (n : ℕ) (i : Fin n) :
    ((⊤ : SimpleGraph (Fin n)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i = n - 1 ∨
    ((⊤ : SimpleGraph (Fin n)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i = -1 := by
  set μ := ((⊤ : SimpleGraph (Fin n)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i
  obtain ⟨v, hv0, hv⟩ := exists_eigvec ((⊤ : SimpleGraph (Fin n)).isHermitian_adjMatrix (R := ℝ)) i
  have key : ∀ u, (μ + 1) * v u = ∑ w, v w := by
    intro u
    have h := congrFun hv u
    have hs := Finset.sum_compl_add_sum {u} v
    rw [adjMatrix_mulVec_apply, neighborFinset_top] at h
    simp only [Finset.sum_singleton, Pi.smul_apply, smul_eq_mul] at h hs
    linarith
  have hsum : (μ + 1) * ∑ w, v w = n * ∑ w, v w := by
    rw [Finset.mul_sum]
    simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hS : ∑ w, v w = 0
  · right
    obtain ⟨u, hu⟩ : ∃ u, v u ≠ 0 := by
      by_contra hc; push Not at hc; exact hv0 (funext hc)
    have := key u
    rw [hS] at this
    have := (mul_eq_zero.mp this).resolve_right hu
    linarith
  · left
    have := mul_right_cancel₀ hS hsum
    linarith

theorem energy_top (n : ℕ) (hn : 1 ≤ n) : energy (⊤ : SimpleGraph (Fin n)) = 2 * ((n : ℝ) - 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [energy_eq_sum _ (fun μ => ((n - 2) * μ + 2 * (n - 1)) / n)]
  · rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_eig, trace_adjMatrix]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro i
    rcases eig_top n i with h | h <;> rw [h]
    · rw [abs_of_nonneg (by linarith)]; field_simp; ring
    · rw [abs_neg, abs_one]; field_simp; ring

/-! ## Complete bipartite graphs: `E(K_{a,b}) = 2√(ab)` -/

instance (a b : ℕ) : DecidableRel (completeBipartiteGraph (Fin a) (Fin b)).Adj := fun u w =>
  inferInstanceAs (Decidable (u.isLeft ∧ w.isRight ∨ u.isRight ∧ w.isLeft))

lemma eig_cb (a b : ℕ) (i : Fin a ⊕ Fin b) :
    ((completeBipartiteGraph (Fin a) (Fin b)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i = 0 ∨
    ((completeBipartiteGraph (Fin a) (Fin b)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i ^ 2 =
      a * b := by
  set μ := ((completeBipartiteGraph (Fin a) (Fin b)).isHermitian_adjMatrix (R := ℝ)).eigenvalues i
  obtain ⟨v, hv0, hv⟩ :=
    exists_eigvec ((completeBipartiteGraph (Fin a) (Fin b)).isHermitian_adjMatrix (R := ℝ)) i
  set S := ∑ l : Fin a, v (Sum.inl l)
  set T := ∑ r : Fin b, v (Sum.inr r)
  have hl : ∀ l, μ * v (Sum.inl l) = T := by
    intro l
    have h := congrFun hv (Sum.inl l)
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, adjMatrix_apply,
      completeBipartiteGraph_adj, Pi.smul_apply, smul_eq_mul] at h
    simpa [T] using h.symm
  have hr : ∀ r, μ * v (Sum.inr r) = S := by
    intro r
    have h := congrFun hv (Sum.inr r)
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, adjMatrix_apply,
      completeBipartiteGraph_adj, Pi.smul_apply, smul_eq_mul] at h
    simpa [S] using h.symm
  have hS : μ * S = a * T := by
    rw [Finset.mul_sum]; simp [hl]
  have hT : μ * T = b * S := by
    rw [Finset.mul_sum]; simp [hr]
  by_contra hc
  push Not at hc
  obtain ⟨h0, h2⟩ := hc
  have hS0 : S = 0 := by
    have : (μ ^ 2 - a * b) * S = 0 := by linear_combination μ * hS + a * hT
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  have hT0 : T = 0 := by
    have : (μ ^ 2 - a * b) * T = 0 := by linear_combination μ * hT + b * hS
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  apply hv0
  funext u
  rcases u with l | r
  · have := hl l; rw [hT0] at this; exact (mul_eq_zero.mp this).resolve_left h0
  · have := hr r; rw [hS0] at this; exact (mul_eq_zero.mp this).resolve_left h0

lemma card_edges_cb (a b : ℕ) :
    ((completeBipartiteGraph (Fin a) (Fin b)).adjMatrix ℝ *
      (completeBipartiteGraph (Fin a) (Fin b)).adjMatrix ℝ).trace = 2 * (a * b) := by
  simp [trace, Matrix.diag, mul_apply, Fintype.sum_sum_type, adjMatrix_apply]
  ring

theorem energy_cb (a b : ℕ) :
    energy (completeBipartiteGraph (Fin a) (Fin b)) = 2 * Real.sqrt (a * b) := by
  rcases Nat.eq_zero_or_pos (a * b) with hab | hab
  · have hab' : (a : ℝ) * b = 0 := by exact_mod_cast hab
    rw [hab', Real.sqrt_zero, mul_zero]
    unfold energy
    apply Finset.sum_eq_zero
    intro i _
    rcases eig_cb a b i with h | h
    · rw [h, abs_zero]
    · rw [hab'] at h; rw [pow_eq_zero_iff (by norm_num) |>.mp h, abs_zero]
  · have hab' : (0 : ℝ) < a * b := by exact_mod_cast hab
    have hsq := Real.sqrt_pos.mpr hab'
    rw [energy_eq_sum _ (fun μ => μ ^ 2 / Real.sqrt (a * b))]
    · rw [← Finset.sum_div, sum_eig_sq, card_edges_cb]
      field_simp
      rw [Real.sq_sqrt hab'.le]
    · intro i
      rcases eig_cb a b i with h | h
      · rw [h]; simp
      · rw [h, ← Real.sqrt_sq_eq_abs, h]
        field_simp
        rw [Real.sq_sqrt hab'.le]

theorem energy_cb_le (a b : ℕ) :
    energy (completeBipartiteGraph (Fin a) (Fin b)) ≤ (a + b : ℕ) := by
  rw [energy_cb]
  have h1 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have h2 : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (2 * Real.sqrt (a * b) - (a + b))]

/-! ## Trees on 4 vertices: the star `K_{1,3}` and the path `P_4` -/

/-- The star `K_{1,3}` on `Fin 4` with centre `0`. -/
def star4 : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun i j => i = 0 ∨ j = 0)

instance : DecidableRel star4.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i = 0 ∨ j = 0) ∨ (j = 0 ∨ i = 0))))

instance (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

lemma adj_star4 : star4.adjMatrix ℝ = !![0,1,1,1; 1,0,0,0; 1,0,0,0; 1,0,0,0] := by
  ext i j; rw [adjMatrix_apply]; fin_cases i <;> fin_cases j <;> simp [star4]

lemma adj_P4 : (pathGraph 4).adjMatrix ℝ = !![0,1,0,0; 1,0,1,0; 0,1,0,1; 0,0,1,0] := by
  ext i j; rw [adjMatrix_apply]; fin_cases i <;> fin_cases j <;> simp [pathGraph_adj]

theorem star4_isTree : star4.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨⟨fun u v => ?_⟩, ?_⟩
  · have h : ∀ u, star4.Reachable 0 u := fun u => by
      by_cases hu : u = 0
      · subst hu; rfl
      · exact Adj.reachable (by simp [star4]; exact Ne.symm hu)
    exact (h u).symm.trans (h v)
  · rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem pathGraph4_isTree : (pathGraph 4).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected 3, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

lemma eig_star4 (i : Fin 4) :
    (star4.isHermitian_adjMatrix (R := ℝ)).eigenvalues i = 0 ∨
    (star4.isHermitian_adjMatrix (R := ℝ)).eigenvalues i ^ 2 = 3 := by
  set μ := (star4.isHermitian_adjMatrix (R := ℝ)).eigenvalues i
  obtain ⟨v, hv0, hv⟩ := exists_eigvec (star4.isHermitian_adjMatrix (R := ℝ)) i
  change _ *ᵥ v = μ • v at hv
  rw [adj_star4] at hv
  have e0 := congrFun hv 0; have e1 := congrFun hv 1
  have e2 := congrFun hv 2; have e3 := congrFun hv 3
  simp [mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  by_contra hc
  push Not at hc
  obtain ⟨h0, h2⟩ := hc
  have hv00 : v 0 = 0 := by
    have : (μ ^ 2 - 3) * v 0 = 0 := by linear_combination (-μ) * e0 - e1 - e2 - e3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  have hv1 : v 1 = 0 := by rw [hv00] at e1; exact (mul_eq_zero.mp e1.symm).resolve_left h0
  have hv2 : v 2 = 0 := by rw [hv00] at e2; exact (mul_eq_zero.mp e2.symm).resolve_left h0
  have hv3 : v 3 = 0 := by rw [hv00] at e3; exact (mul_eq_zero.mp e3.symm).resolve_left h0
  apply hv0
  funext u
  fin_cases u
  · exact hv00
  · exact hv1
  · exact hv2
  · exact hv3

lemma eig_P4 (i : Fin 4) :
    ((pathGraph 4).isHermitian_adjMatrix (R := ℝ)).eigenvalues i ^ 4 -
      3 * ((pathGraph 4).isHermitian_adjMatrix (R := ℝ)).eigenvalues i ^ 2 + 1 = 0 := by
  set μ := ((pathGraph 4).isHermitian_adjMatrix (R := ℝ)).eigenvalues i
  obtain ⟨v, hv0, hv⟩ := exists_eigvec ((pathGraph 4).isHermitian_adjMatrix (R := ℝ)) i
  change _ *ᵥ v = μ • v at hv
  rw [adj_P4] at hv
  have e0 := congrFun hv 0; have e1 := congrFun hv 1
  have e2 := congrFun hv 2; have e3 := congrFun hv 3
  simp [mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  -- `v 1 = μ v0`, `v 2 = (μ²-1) v0`, `v 3 = (μ³-2μ) v0`, and `μ v3 = v2`
  by_contra hc
  have hv00 : v 0 = 0 := by
    have : (μ ^ 4 - 3 * μ ^ 2 + 1) * v 0 = 0 := by
      linear_combination (2 * μ - μ ^ 3) * e0 + (1 - μ ^ 2) * e1 - μ * e2 - e3
    exact (mul_eq_zero.mp this).resolve_left hc
  have hv1 : v 1 = 0 := by rw [hv00] at e0; linarith
  have hv2 : v 2 = 0 := by rw [hv00, hv1] at e1; linarith
  have hv3 : v 3 = 0 := by rw [hv1, hv2] at e2; linarith
  apply hv0
  funext u
  fin_cases u
  · exact hv00
  · exact hv1
  · exact hv2
  · exact hv3

theorem energy_star4 : energy star4 = 2 * Real.sqrt 3 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [energy_eq_sum _ (fun μ => μ ^ 2 / Real.sqrt 3)]
  · rw [← Finset.sum_div, sum_eig_sq, adj_star4]
    simp [trace, Matrix.diag, mul_apply, Fin.sum_univ_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  · intro i
    rcases eig_star4 i with h | h
    · rw [h]; simp
    · rw [h, ← Real.sqrt_sq_eq_abs, h]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]

theorem energy_P4 : energy (pathGraph 4) = 2 * Real.sqrt 5 := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h55 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [energy_eq_sum _ (fun μ => (μ ^ 2 + 1) / Real.sqrt 5)]
  · rw [← Finset.sum_div, Finset.sum_add_distrib, sum_eig_sq, adj_P4]
    simp [trace, Matrix.diag, mul_apply, Fin.sum_univ_four]
    field_simp
    nlinarith [h55]
  · intro i
    have hq := eig_P4 i
    set μ := ((pathGraph 4).isHermitian_adjMatrix (R := ℝ)).eigenvalues i
    have hsq : (|μ| * Real.sqrt 5) ^ 2 = (μ ^ 2 + 1) ^ 2 := by
      rw [mul_pow, h55, sq_abs]; nlinarith [hq]
    have hpos : 0 ≤ |μ| * Real.sqrt 5 := by positivity
    have hpos' : 0 ≤ μ ^ 2 + 1 := by positivity
    have heq : |μ| * Real.sqrt 5 = μ ^ 2 + 1 := by
      have := (sq_eq_sq₀ hpos hpos').mp hsq
      exact this
    field_simp
    exact heq

/-! ## The conjecture and its refutation -/

/-- Part (i), reading over all graphs: for every `n` some complete bipartite graph
`K_{a,b}` (`a + b = n`) has maximum energy among all graphs on `n` vertices. -/
def MaxIsCompleteBipartite : Prop :=
  ∀ n : ℕ, ∃ a b : ℕ, a + b = n ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    energy G ≤ energy (completeBipartiteGraph (Fin a) (Fin b))

/-- Part (i), reading over bipartite graphs only. -/
def MaxBipartiteIsCompleteBipartite : Prop :=
  ∀ n : ℕ, ∃ a b : ℕ, a + b = n ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsBipartite → energy G ≤ energy (completeBipartiteGraph (Fin a) (Fin b))

/-- Part (ii): for every `n`, the path has minimum energy among trees on `n` vertices. -/
def MinTreeIsPath : Prop :=
  ∀ n : ℕ, ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj],
    T.IsTree → energy (pathGraph n) ≤ energy T

/-- For every `n ≥ 3`, `K_n` has strictly larger energy than every `K_{a,b}` with `a+b = n`. -/
theorem completeGraph_beats_completeBipartite (n : ℕ) (hn : 3 ≤ n) (a b : ℕ) (hab : a + b = n) :
    energy (completeBipartiteGraph (Fin a) (Fin b)) < energy (⊤ : SimpleGraph (Fin n)) := by
  have h1 := energy_cb_le a b
  rw [energy_top n (by omega)]
  rw [hab] at h1
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem not_maxIsCompleteBipartite : ¬ MaxIsCompleteBipartite := by
  intro h
  obtain ⟨a, b, hab, hmax⟩ := h 3
  have := hmax ⊤
  have := completeGraph_beats_completeBipartite 3 le_rfl a b hab
  linarith

lemma two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 := by
  rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem not_maxBipartiteIsCompleteBipartite : ¬ MaxBipartiteIsCompleteBipartite := by
  intro h
  obtain ⟨a, b, hab, hmax⟩ := h 4
  have hbip : (pathGraph 4).IsBipartite := by
    simpa using (pathGraph.bicoloring 4).colorable
  have h1 := hmax (pathGraph 4) hbip
  have h2 := energy_cb_le a b
  rw [energy_P4] at h1
  rw [hab] at h2
  have := two_lt_sqrt5
  push_cast at h2
  linarith

theorem energy_star4_lt_P4 : energy star4 < energy (pathGraph 4) := by
  rw [energy_star4, energy_P4]
  have : Real.sqrt 3 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem not_minTreeIsPath : ¬ MinTreeIsPath := by
  intro h
  have := h 4 star4 star4_isTree
  have := energy_star4_lt_P4
  linarith

/-- **Main theorem.** Both parts of the conjecture fail. -/
theorem main : ¬ MaxIsCompleteBipartite ∧ ¬ MaxBipartiteIsCompleteBipartite ∧ ¬ MinTreeIsPath :=
  ⟨not_maxIsCompleteBipartite, not_maxBipartiteIsCompleteBipartite, not_minTreeIsPath⟩

end C3730
