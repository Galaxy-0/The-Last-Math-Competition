import Mathlib

/-!
# Conjecture 00000003963: algebraic connectivity of hypercube layers

Statement: "The algebraic connectivity of the induced graph of a layer, a Johnson graph,
attains its minimum over all layers at l = n/2, of order Theta(log n / n^2)."

The layer of weight `ℓ` of the hypercube `Q_n` is identified with the `ℓ`-subsets of `Fin n`.
* Johnson reading: the layer graph is the Johnson graph `J(n,ℓ)` (adjacent iff the subsets meet
  in `ℓ-1` elements).  We prove `λ₂(L(J(n,ℓ))) ≥ n` for all `n` and all `1 ≤ ℓ ≤ n-1`
  (`algConn_johnson_ge`), and `λ₂` of the normalized Laplacian is `≥ n/(ℓ(n-ℓ))`, i.e. `≥ 4/n`
  at `ℓ = n/2`.  Neither is `O(log n / n^2)` (`johnson_not_bigO`, `johnson_norm_not_bigO`).
* Literal reading: the subgraph of `Q_n` induced on a layer has no edges, so `λ₂ = 0`, which is
  not `Ω(log n / n^2)` (`induced_not_bigOmega`).

`λ₂` is the second smallest eigenvalue, counted with multiplicity, of the Hermitian matrix,
read off Mathlib's decreasingly sorted list `Matrix.IsHermitian.eigenvalues₀`.
-/

open Finset Matrix SimpleGraph

namespace C3963

/-! ## Objects -/

/-- The hypercube `Q_n` on subsets of `Fin n` (0/1 vectors): adjacent iff they differ in exactly
one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Finset (Fin n)) where
  Adj s t := (symmDiff s t).card = 1
  symm := ⟨fun s t h => by rwa [symmDiff_comm]⟩
  loopless := ⟨fun s h => by simp at h⟩

instance (n : ℕ) : DecidableRel (hypercube n).Adj := fun s t =>
  inferInstanceAs (Decidable ((symmDiff s t).card = 1))

/-- The layer of weight `ℓ` of `Q_n`. -/
abbrev Layer (n ℓ : ℕ) := {s : Finset (Fin n) // s.card = ℓ}

/-- The Johnson graph `J(n,ℓ)`: `ℓ`-subsets of `Fin n`, adjacent iff they share `ℓ-1` elements. -/
def johnson (n ℓ : ℕ) : SimpleGraph (Layer n ℓ) where
  Adj A B := (A.1 ∩ B.1).card + 1 = ℓ
  symm := ⟨fun A B h => by rwa [inter_comm]⟩
  loopless := ⟨fun A h => by simp [A.2] at h⟩

instance (n ℓ : ℕ) : DecidableRel (johnson n ℓ).Adj := fun A B =>
  inferInstanceAs (Decidable ((A.1 ∩ B.1).card + 1 = ℓ))

/-- Second smallest eigenvalue (with multiplicity) of a real symmetric matrix: `eigenvalues₀` is
sorted decreasingly (`eigenvalues₀_antitone`), so this is the entry of index `card - 2`
(set to `0` when there are fewer than two eigenvalues). -/
noncomputable def lambda2 {V : Type*} [Fintype V] [DecidableEq V] {M : Matrix V V ℝ}
    (hM : M.IsHermitian) : ℝ :=
  if h : 2 ≤ Fintype.card V then hM.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else 0

/-- Algebraic connectivity (Fiedler): second smallest eigenvalue of the Laplacian `L = D - A`. -/
noncomputable def algConn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  lambda2 (G.isHermitian_lapMatrix (R := ℝ))

/-- Normalized Laplacian `I - D^{-1/2} A D^{-1/2}` (diagonal entry `0` at isolated vertices). -/
noncomputable def normLap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℝ := fun i j =>
  if i = j then (if G.degree i = 0 then 0 else 1)
  else if G.Adj i j then -1 / Real.sqrt (G.degree i * G.degree j) else 0

lemma normLap_isHermitian {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (normLap G).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, normLap]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases ha : G.Adj i j
    · rw [if_pos ha, if_pos ha.symm, mul_comm]
    · rw [if_neg ha, if_neg (fun h' => ha h'.symm)]

/-! ## A variational lower bound for `λ₂` -/

theorem lambda2_ge {V : Type*} [Fintype V] [DecidableEq V] {M : Matrix V V ℝ}
    (hM : M.IsHermitian) {c : ℝ} (hc : 0 < c) (h1 : M *ᵥ (fun _ => 1) = 0)
    (hq : ∀ x : V → ℝ, ∑ i, x i = 0 → c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (M *ᵥ x))
    (hV : 2 ≤ Fintype.card V) : c ≤ lambda2 hM := by
  set v : V → V → ℝ := fun j => ⇑(hM.eigenvectorBasis j)
  have hon : ∀ i j, ∑ t, v i t * v j t = if i = j then 1 else 0 := by
    intro i j
    rw [← orthonormal_iff_ite.1 hM.eigenvectorBasis.orthonormal i j]
    simp [v, PiLp.inner_apply, mul_comm]
  have hev : ∀ j, M *ᵥ v j = hM.eigenvalues j • v j := hM.mulVec_eigenvectorBasis
  have hT : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM
  have hsumM : ∀ x, ∑ t, (M *ᵥ x) t = 0 := by
    intro x
    have : (fun _ => (1 : ℝ)) ⬝ᵥ (M *ᵥ x) = 0 := by
      rw [dotProduct_mulVec, ← hT, vecMul_transpose, h1, zero_dotProduct]
    simpa [dotProduct] using this
  have hsq : ∀ j, v j ⬝ᵥ (M *ᵥ v j) = hM.eigenvalues j := by
    intro j; rw [hev, dotProduct_smul, smul_eq_mul]
    have := hon j j; simp only [if_true] at this; simp [dotProduct, this]
  -- every eigenvalue is `0` or `≥ c`
  have step1 : ∀ j, hM.eigenvalues j = 0 ∨ c ≤ hM.eigenvalues j := by
    intro j
    by_cases h0 : hM.eigenvalues j = 0
    · exact Or.inl h0
    right
    have hs : ∑ t, v j t = 0 := by
      have := hsumM (v j); rw [hev] at this
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum] at this
      exact (mul_eq_zero.1 this).resolve_left h0
    have := hq (v j) hs; rw [hsq] at this
    have h11 := hon j j; simp only [if_true] at h11
    simpa [sq, h11] using this
  have hker : ∀ j, hM.eigenvalues j = 0 → ∑ t, v j t ≠ 0 := by
    intro j h0 hs
    have := hq (v j) hs; rw [hsq, h0] at this
    have h11 := hon j j; simp only [if_true] at h11
    simp only [sq, h11] at this; linarith
  -- at most one eigenvalue vanishes
  have step2 : ∀ i j, i ≠ j → hM.eigenvalues i = 0 → hM.eigenvalues j = 0 → False := by
    intro i j hij hi hj
    set a := ∑ t, v j t
    set b := ∑ t, v i t
    have hx : (fun t => a * v i t - b * v j t) = a • v i - b • v j := by
      funext t; simp
    have hMx : M *ᵥ (fun t => a * v i t - b * v j t) = 0 := by
      rw [hx, mulVec_sub, mulVec_smul, mulVec_smul, hev, hev, hi, hj]; simp
    have hs : ∑ t, (a * v i t - b * v j t) = 0 := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum]; ring
    have := hq _ hs
    rw [hMx, dotProduct_zero] at this
    have hexp : ∑ t, (a * v i t - b * v j t) ^ 2 =
        a ^ 2 * ∑ t, v i t * v i t - 2 * a * b * ∑ t, v i t * v j t + b ^ 2 * ∑ t, v j t * v j t := by
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun t _ => by ring
    rw [hexp, hon, hon, hon, if_pos rfl, if_pos rfl, if_neg hij] at this
    have hb := hker i hi
    have : 0 < b ^ 2 := by positivity
    nlinarith [sq_nonneg a]
  -- conclude via the sorted list
  unfold lambda2; rw [dif_pos hV]
  by_contra hlt; push Not at hlt
  set N := Fintype.card V
  let e : Fin N ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hval : ∀ k : Fin N, hM.eigenvalues (e k) = hM.eigenvalues₀ k := by
    intro k; simp [IsHermitian.eigenvalues, e]
  have hle : hM.eigenvalues₀ ⟨N - 1, by omega⟩ ≤ hM.eigenvalues₀ ⟨N - 2, by omega⟩ :=
    hM.eigenvalues₀_antitone (Fin.mk_le_mk.2 (by omega))
  have hne : e ⟨N - 2, by omega⟩ ≠ e ⟨N - 1, by omega⟩ := by
    intro h; have := Fin.mk.inj_iff.1 (e.injective h); omega
  have z1 := (step1 (e ⟨N - 2, by omega⟩)).resolve_right (by rw [hval]; linarith)
  have z2 := (step1 (e ⟨N - 1, by omega⟩)).resolve_right (by rw [hval]; linarith)
  exact step2 _ _ hne z1 z2

/-! ## Up and down operators on functions of subsets -/

variable {n : ℕ}

/-- `lvl n m`: the `m`-subsets of `Fin n`. -/
abbrev lvl (n m : ℕ) : Finset (Finset (Fin n)) := powersetCard m univ

/-- Down operator: `dn f C = ∑_{i ∉ C} f (C ∪ {i})`. -/
def dn (f : Finset (Fin n) → ℝ) (C : Finset (Fin n)) : ℝ := ∑ i ∈ Cᶜ, f (insert i C)

/-- Up operator: `up f E = ∑_{i ∈ E} f (E \ {i})`. -/
def up (f : Finset (Fin n) → ℝ) (E : Finset (Fin n)) : ℝ := ∑ i ∈ E, f (E.erase i)

/-- Sum of `f` over all swaps `A - {j} + {i}` (the Johnson neighbours of `A`). -/
def cross (f : Finset (Fin n) → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ j ∈ A, ∑ i ∈ Aᶜ, f (insert i (A.erase j))

lemma up_dn (f : Finset (Fin n) → ℝ) (A : Finset (Fin n)) :
    up (dn f) A = A.card * f A + cross f A := by
  unfold up dn cross
  rw [card_eq_sum_ones, Nat.cast_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [compl_erase, sum_insert (by simp [hj]), insert_erase hj]
  simp

lemma dn_up (f : Finset (Fin n) → ℝ) (A : Finset (Fin n)) :
    dn (up f) A = ((n : ℝ) - A.card) * f A + cross f A := by
  unfold up dn cross
  have hc : ((Aᶜ).card : ℝ) = n - A.card := by
    rw [card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using card_le_univ A)]
  rw [sum_comm (s := A), ← hc, card_eq_sum_ones, Nat.cast_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hiA : i ∉ A := mem_compl.1 hi
  dsimp only
  rw [sum_insert hiA, erase_insert hiA, Nat.cast_one, one_mul]
  congr 1
  exact sum_congr rfl fun j hj => by rw [erase_insert_of_ne (show i ≠ j from fun h => hiA (h ▸ hj))]

/-- `up` and `dn` are adjoint between consecutive levels. -/
lemma adjoint (m : ℕ) (g h : Finset (Fin n) → ℝ) :
    ∑ E ∈ lvl n (m + 1), g E * up h E = ∑ A ∈ lvl n m, h A * dn g A := by
  unfold up dn
  simp only [mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun i => (lvl n (m + 1)).filter (i ∈ ·)) (fun E i => by simp),
    sum_comm' (t' := univ) (s' := fun i => (lvl n m).filter (i ∉ ·)) (fun A i => by simp)]
  refine sum_congr rfl fun i _ => ?_
  refine sum_nbij' (fun E => E.erase i) (fun A => insert i A) ?_ ?_ ?_ ?_ ?_
  · intro E hE
    simp only [mem_filter, mem_powersetCard_univ] at hE ⊢
    exact ⟨by simp [card_erase_of_mem hE.2, hE.1], notMem_erase i E⟩
  · intro A hA
    simp only [mem_filter, mem_powersetCard_univ] at hA ⊢
    exact ⟨by rw [card_insert_of_notMem hA.2, hA.1], mem_insert_self i A⟩
  · intro E hE; simp only [mem_filter] at hE; exact insert_erase hE.2
  · intro A hA; simp only [mem_filter] at hA; exact erase_insert hA.2
  · intro E hE; simp only [mem_filter] at hE; rw [insert_erase hE.2, mul_comm]

lemma sum_dn (m : ℕ) (g : Finset (Fin n) → ℝ) :
    ∑ A ∈ lvl n m, dn g A = (m + 1) * ∑ E ∈ lvl n (m + 1), g E := by
  have := adjoint m g (fun _ => 1)
  simp only [up, sum_const, one_mul, nsmul_eq_mul, mul_one] at this
  rw [mul_sum, ← this]
  refine sum_congr rfl fun E hE => ?_
  rw [mem_powersetCard_univ.1 hE]; push_cast; ring

/-- Key inequality, by induction on the level: for `f` of mean zero on `(m+1)`-sets,
`‖dn f‖² ≤ m (n - m - 1) ‖f‖²`. -/
lemma key (m : ℕ) (hm : m + 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hf : ∑ A ∈ lvl n (m + 1), f A = 0) :
    ∑ C ∈ lvl n m, dn f C ^ 2 ≤ m * ((n : ℝ) - m - 1) * ∑ A ∈ lvl n (m + 1), f A ^ 2 := by
  induction m generalizing f with
  | zero =>
    have h := sum_dn 0 f
    rw [hf, mul_zero] at h
    simp only [lvl, powersetCard_zero, sum_singleton] at h ⊢
    simp [h]
  | succ m ih =>
    set z := dn f with hz_def
    have hz : ∑ A ∈ lvl n (m + 1), z A = 0 := by rw [sum_dn, hf, mul_zero]
    have h1 : ∑ A ∈ lvl n (m + 1), z A ^ 2 = ∑ E ∈ lvl n (m + 1 + 1), f E * up z E := by
      rw [adjoint]; simp only [sq]; rfl
    have h2 : ∑ E ∈ lvl n (m + 1 + 1), up z E ^ 2 = ∑ C ∈ lvl n m, dn z C ^ 2
        + ((n : ℝ) - 2 * (m + 1)) * ∑ A ∈ lvl n (m + 1), z A ^ 2 := by
      have a1 := adjoint (m + 1) (up z) z
      have a2 := adjoint m z (dn z)
      simp only [sq]
      rw [a1, ← a2, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun A hA => ?_
      rw [dn_up, up_dn, mem_powersetCard_univ.1 hA]; push_cast; ring
    have h3 := ih (by omega) z hz
    have h4 := sum_mul_sq_le_sq_mul_sq (lvl n (m + 1 + 1)) f (up z)
    rw [← h1, h2] at h4
    set Z := ∑ A ∈ lvl n (m + 1), z A ^ 2
    set F := ∑ E ∈ lvl n (m + 1 + 1), f E ^ 2
    have hZ : 0 ≤ Z := sum_nonneg fun _ _ => sq_nonneg _
    have hF : 0 ≤ F := sum_nonneg fun _ _ => sq_nonneg _
    have hmn : (m : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : m + 2 ≤ n)
    have hc : (0 : ℝ) ≤ (m + 1) * (n - (m + 1) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    push_cast
    rcases hZ.eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg hc hF
    · have : Z * Z ≤ Z * ((m + 1) * (n - (m + 1) - 1) * F) := by
        nlinarith [mul_le_mul_of_nonneg_left h3 hF]
      exact le_of_mul_le_mul_left this hpos

/-! ## The Johnson Laplacian in terms of `up` and `dn` -/

/-- Extension by zero of a function on a layer. -/
def extz {k : ℕ} (x : Layer n k → ℝ) (s : Finset (Fin n)) : ℝ :=
  if h : s.card = k then x ⟨s, h⟩ else 0

lemma extz_apply {k : ℕ} (x : Layer n k → ℝ) (A : Layer n k) : extz x A.1 = x A := by
  simp [extz, A.2]

lemma sum_layer {k : ℕ} (F : Finset (Fin n) → ℝ) :
    ∑ A : Layer n k, F A.1 = ∑ s ∈ lvl n k, F s :=
  (sum_subtype _ (fun s => by simp) F).symm

lemma swap_card {A : Finset (Fin n)} {i j : Fin n} (hj : j ∈ A) (hi : i ∉ A) :
    (insert i (A.erase j)).card = A.card := by
  rw [card_insert_of_notMem (fun h => hi (mem_of_mem_erase h)), card_erase_of_mem hj]
  have := card_pos.2 ⟨j, hj⟩; omega

lemma nbr_sum {k : ℕ} (x : Layer n k → ℝ) (A : Layer n k) :
    ∑ B ∈ (johnson n k).neighborFinset A, x B = cross (extz x) A.1 := by
  calc ∑ B ∈ (johnson n k).neighborFinset A, x B
      = ∑ B : Layer n k, (fun s => if (A.1 ∩ s).card + 1 = k then extz x s else 0) B.1 := by
        rw [neighborFinset_eq_filter, sum_filter]
        exact sum_congr rfl fun B _ => by simp only [extz_apply]; rfl
    _ = ∑ s ∈ (lvl n k).filter (fun s => (A.1 ∩ s).card + 1 = k), extz x s := by
        rw [sum_filter]
        exact sum_layer (k := k) (fun s => if (A.1 ∩ s).card + 1 = k then extz x s else 0)
    _ = ∑ p ∈ A.1 ×ˢ A.1ᶜ, extz x (insert p.2 (A.1.erase p.1)) := by
        symm
        refine sum_bij (fun p _ => insert p.2 (A.1.erase p.1)) ?_ ?_ ?_ (fun _ _ => rfl)
        · rintro ⟨j, i⟩ hp
          simp only [mem_product, mem_compl] at hp
          have hint : A.1 ∩ insert i (A.1.erase j) = A.1.erase j := by
            ext t; simp only [mem_inter, mem_insert, mem_erase]
            constructor
            · rintro ⟨htA, rfl | h⟩
              · exact absurd htA hp.2
              · exact h
            · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inr ⟨h1, h2⟩⟩
          simp only [mem_filter, mem_powersetCard_univ]
          refine ⟨by rw [swap_card hp.1 hp.2, A.2], ?_⟩
          rw [hint, card_erase_of_mem hp.1, A.2]
          have := card_pos.2 ⟨j, hp.1⟩; rw [A.2] at this; omega
        · rintro ⟨j, i⟩ h1 ⟨j', i'⟩ h2 heq
          simp only [mem_product, mem_compl] at h1 h2
          dsimp only at heq
          have hi : i = i' := by
            have : i ∈ insert i' (A.1.erase j') := by rw [← heq]; exact mem_insert_self i _
            rcases mem_insert.1 this with h | h
            · exact h
            · exact absurd (mem_of_mem_erase h) h1.2
          have hj : j = j' := by
            by_contra hne
            have : j ∈ insert i (A.1.erase j) := by
              rw [heq]; exact mem_insert_of_mem (mem_erase.2 ⟨hne, h1.1⟩)
            rcases mem_insert.1 this with h | h
            · exact h1.2 (h ▸ h1.1)
            · exact notMem_erase j _ h
          rw [hi, hj]
        · intro s hs
          simp only [mem_filter, mem_powersetCard_univ] at hs
          obtain ⟨hsk, hint⟩ := hs
          have e1 : (A.1 \ s).card = 1 := by
            have := card_sdiff_add_card_inter A.1 s; rw [A.2] at this; omega
          have e2 : (s \ A.1).card = 1 := by
            have := card_sdiff_add_card_inter s A.1; rw [hsk, inter_comm] at this; omega
          obtain ⟨j, hj⟩ := card_eq_one.1 e1
          obtain ⟨i, hi⟩ := card_eq_one.1 e2
          have hj' : ∀ t, t ∈ A.1 ∧ t ∉ s ↔ t = j := fun t => by
            rw [← mem_sdiff, hj, mem_singleton]
          have hi' : ∀ t, t ∈ s ∧ t ∉ A.1 ↔ t = i := fun t => by
            rw [← mem_sdiff, hi, mem_singleton]
          refine ⟨(j, i), ?_, ?_⟩
          · simp only [mem_product, mem_compl]
            exact ⟨((hj' j).2 rfl).1, ((hi' i).2 rfl).2⟩
          · show insert i (A.1.erase j) = s
            ext t; simp only [mem_insert, mem_erase]
            have := hj' t; have := hi' t; tauto
    _ = cross (extz x) A.1 := by rw [sum_product]; rfl

lemma degree_johnson {k : ℕ} (A : Layer n k) :
    ((johnson n k).degree A : ℝ) = k * ((n : ℝ) - k) := by
  have h := nbr_sum (fun _ => (1 : ℝ)) A
  rw [sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree] at h
  rw [h]; unfold cross
  have hc : ((A.1ᶜ).card : ℝ) = n - k := by
    rw [card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using card_le_univ A.1),
      A.2]
  rw [sum_congr rfl fun j hj => sum_congr rfl fun i hi =>
    (show extz (fun _ => (1 : ℝ)) (insert i (A.1.erase j)) = 1 by
      simp [extz, swap_card hj (mem_compl.1 hi), A.2])]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [hc, A.2]

/-- Laplacian quadratic form bound on `J(n, m+1)`: `x ⊥ 1 → xᵀ L x ≥ n ‖x‖²`. -/
theorem johnson_quad (m : ℕ) (hm : m + 1 ≤ n) (x : Layer n (m + 1) → ℝ) (hx : ∑ A, x A = 0) :
    (n : ℝ) * ∑ A, x A ^ 2 ≤ x ⬝ᵥ ((johnson n (m + 1)).lapMatrix ℝ *ᵥ x) := by
  set f := extz x with hf_def
  set c : ℝ := (m + 1) * ((n : ℝ) - (m + 1)) + (m + 1)
  have hL : ∀ A : Layer n (m + 1), ((johnson n (m + 1)).lapMatrix ℝ *ᵥ x) A =
      c * f A.1 - up (dn f) A.1 := by
    intro A
    rw [lapMatrix_mulVec_apply, degree_johnson, nbr_sum, up_dn, A.2, hf_def, extz_apply]
    push_cast; ring
  have hf0 : ∑ s ∈ lvl n (m + 1), f s = 0 := by
    rw [← sum_layer]; simpa only [hf_def, extz_apply] using hx
  have hq : x ⬝ᵥ ((johnson n (m + 1)).lapMatrix ℝ *ᵥ x) =
      c * ∑ s ∈ lvl n (m + 1), f s ^ 2 - ∑ C ∈ lvl n m, dn f C ^ 2 := by
    have e1 : ∀ A : Layer n (m + 1), x A * ((johnson n (m + 1)).lapMatrix ℝ *ᵥ x) A =
        f A.1 * (c * f A.1 - up (dn f) A.1) := fun A => by rw [hL, hf_def, extz_apply]
    rw [dotProduct, sum_congr rfl fun A _ => e1 A,
      sum_layer (fun s => f s * (c * f s - up (dn f) s))]
    simp only [mul_sub, sum_sub_distrib]
    rw [adjoint m f (dn f), mul_sum]
    simp only [sq]
    congr 1
    exact sum_congr rfl fun s _ => by ring
  have hS : ∑ A, x A ^ 2 = ∑ s ∈ lvl n (m + 1), f s ^ 2 := by
    rw [← sum_layer]; simp only [hf_def, extz_apply]
  rw [hq, hS]
  have hk := key m hm f hf0
  nlinarith [hk]

lemma two_le_card (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) : 2 ≤ Fintype.card (Layer n k) := by
  rw [Fintype.card_finset_len, Fintype.card_fin]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have := Nat.choose_pos (show k' ≤ n' by omega)
  have := Nat.choose_pos (show k' + 1 ≤ n' by omega)
  omega

/-! ## Spectral conclusions -/

/-- Johnson reading: `λ₂(L(J(n,k))) ≥ n` for every `n` and every layer `1 ≤ k ≤ n - 1`. -/
theorem algConn_johnson_ge (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (n : ℝ) ≤ algConn (johnson n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact lambda2_ge _ (by exact_mod_cast (show 0 < n by omega))
    (SimpleGraph.lapMatrix_mulVec_const_eq_zero (G := johnson n (m + 1)) (R := ℝ))
    (johnson_quad m (by omega)) (two_le_card (n := n) _ hk hkn)

lemma lap_apply {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : V) : G.lapMatrix ℝ i j = (if i = j then (G.degree i : ℝ) else 0)
      - (if G.Adj i j then 1 else 0) := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, diagonal_apply]

lemma lambda2_zero {V : Type*} [Fintype V] [DecidableEq V] {M : Matrix V V ℝ}
    (hM : M.IsHermitian) (h0 : M = 0) : lambda2 hM = 0 := by
  unfold lambda2; split_ifs with h
  · have hz := hM.eigenvalues_eq_zero_iff.2 h0
    have := congrFun hz (Fintype.equivOfCardEq (Fintype.card_fin _) ⟨Fintype.card V - 2, by omega⟩)
    simpa [IsHermitian.eigenvalues] using this
  · rfl

lemma normLap_johnson (m : ℕ) (hm : m + 1 + 1 ≤ n) :
    normLap (johnson n (m + 1)) =
      (1 / ((m + 1) * ((n : ℝ) - (m + 1)))) • (johnson n (m + 1)).lapMatrix ℝ := by
  have hmn : (m : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : m + 2 ≤ n)
  have hd : 0 < ((m : ℝ) + 1) * ((n : ℝ) - (m + 1)) := mul_pos (by positivity) (by linarith)
  have hdeg : ∀ A, ((johnson n (m + 1)).degree A : ℝ) = (m + 1) * ((n : ℝ) - (m + 1)) :=
    fun A => by rw [degree_johnson]; push_cast; ring
  have hdeg0 : ∀ A, (johnson n (m + 1)).degree A ≠ 0 := fun A h => by
    have := hdeg A; rw [h] at this; push_cast at this; linarith
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, lap_apply]
  by_cases h : i = j
  · subst h
    simp only [normLap, if_true, if_neg (hdeg0 i), hdeg, SimpleGraph.irrefl, if_false, sub_zero]
    exact (one_div_mul_cancel hd.ne').symm
  · by_cases ha : (johnson n (m + 1)).Adj i j
    · simp only [normLap, if_neg h, if_pos ha, hdeg, Real.sqrt_mul_self hd.le, zero_sub]; ring
    · simp only [normLap, if_neg h, if_neg ha, sub_zero, mul_zero]

/-- Normalized reading: `λ₂(ℒ(J(n,k))) ≥ n / (k (n - k))`. -/
theorem normConn_johnson_ge (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (n : ℝ) / (k * ((n : ℝ) - k)) ≤ lambda2 (normLap_isHermitian (johnson n k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmn : (m : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : m + 2 ≤ n)
  have hd : 0 < ((m : ℝ) + 1) * ((n : ℝ) - (m + 1)) := mul_pos (by positivity) (by linarith)
  push_cast
  refine lambda2_ge _ (div_pos (by linarith) hd) ?_ ?_ (two_le_card (n := n) _ hk hkn)
  · rw [normLap_johnson m hkn, smul_mulVec,
      SimpleGraph.lapMatrix_mulVec_const_eq_zero (G := johnson n (m + 1)) (R := ℝ), smul_zero]
  · intro x hx
    rw [normLap_johnson m hkn, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have := johnson_quad m (by omega) x hx
    calc (n : ℝ) / ((m + 1) * ((n : ℝ) - (m + 1))) * ∑ i, x i ^ 2
        = 1 / ((m + 1) * ((n : ℝ) - (m + 1))) * ((n : ℝ) * ∑ i, x i ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-- The subgraph of `Q_n` induced on the layer of weight `ℓ` (literal reading). -/
abbrev inducedLayer (n ℓ : ℕ) := (hypercube n).induce {s | s.card = ℓ}

lemma inducedLayer_no_adj (n ℓ : ℕ) (u v : {s : Finset (Fin n) | s.card = ℓ}) :
    ¬ (inducedLayer n ℓ).Adj u v := by
  intro h
  change (symmDiff u.1 v.1).card = 1 at h
  have hu : u.1.card = ℓ := u.2
  have hv : v.1.card = ℓ := v.2
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff] at h
  have h1 := card_sdiff_add_card_inter u.1 v.1
  have h2 := card_sdiff_add_card_inter v.1 u.1
  rw [inter_comm] at h2
  omega

/-- Literal reading: every layer's induced subgraph has `λ₂ = 0` (it has no edges). -/
theorem algConn_inducedLayer (n ℓ : ℕ) : algConn (inducedLayer n ℓ) = 0 := by
  have hdeg : ∀ u, (inducedLayer n ℓ).degree u = 0 := fun u => by
    rw [← card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
    intro v hv; exact inducedLayer_no_adj n ℓ u v ((mem_neighborFinset _ _ _).1 hv)
  have hL : (inducedLayer n ℓ).lapMatrix ℝ = 0 := by
    ext u v
    rw [lap_apply, if_neg (inducedLayer_no_adj n ℓ u v), hdeg]; simp
  exact lambda2_zero _ hL

/-! ## Asymptotics -/

lemma exists_large (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Even n ∧ 2 ≤ n ∧ C * Real.log n < 4 * n := by
  obtain ⟨M, hM⟩ := exists_nat_ge (C ^ 2)
  refine ⟨2 * (N + M + 1), by omega, ⟨N + M + 1, by ring⟩, by omega, ?_⟩
  set x : ℝ := ((2 * (N + M + 1) : ℕ) : ℝ)
  have hx : (M : ℝ) + 2 ≤ x := by
    simp only [x]; push_cast; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N), (M.cast_nonneg : (0 : ℝ) ≤ M)]
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x < 2 * Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx0)
    rw [Real.log_sqrt hx0.le] at h1; linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rcases le_or_gt C 0 with hC | hC
  · nlinarith
  · have hCs : C ≤ Real.sqrt x := (le_abs_self C).trans (Real.abs_le_sqrt (by linarith))
    nlinarith [mul_lt_mul_of_pos_left hlog hC, mul_le_mul_of_nonneg_right hCs hs0]

/-- **Refutation (Johnson reading).** The minimum of `λ₂(J(n,k))` over the layers
`1 ≤ k ≤ n - 1` is not `O(log n / n²)` along even `n` (so it is not `Θ(log n / n²)`). -/
theorem johnson_min_not_bigO :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ k, 1 ≤ k ∧ k + 1 ≤ n ∧ algConn (johnson n k) ≤ C * Real.log n / (n : ℝ) ^ 2 := by
  rintro ⟨C, N, h⟩
  obtain ⟨n, hN, he, h2, hlt⟩ := exists_large C N
  obtain ⟨k, hk, hkn, hle⟩ := h n hN he
  have hge := algConn_johnson_ge n k hk hkn
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have : C * Real.log n / (n : ℝ) ^ 2 < n := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- **Refutation (Johnson reading, middle layer).** `λ₂(J(n, n/2))` is not `O(log n / n²)`. -/
theorem johnson_not_bigO :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      algConn (johnson n (n / 2)) ≤ C * Real.log n / (n : ℝ) ^ 2 := by
  rintro ⟨C, N, h⟩
  refine johnson_min_not_bigO ⟨C, N + 2, fun n hn he => ⟨n / 2, by omega, by omega, h n (by omega) he⟩⟩

/-- **Refutation (normalized Laplacian, middle layer).** `λ₂(ℒ(J(n, n/2))) ≥ 4/n` is not
`O(log n / n²)`. -/
theorem johnson_norm_not_bigO :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      lambda2 (normLap_isHermitian (johnson n (n / 2))) ≤ C * Real.log n / (n : ℝ) ^ 2 := by
  rintro ⟨C, N, h⟩
  obtain ⟨n, hN, ⟨t, rfl⟩, h2, hlt⟩ := exists_large C N
  have ht : (t + t) / 2 = t := by omega
  have hge := normConn_johnson_ge (t + t) t (by omega) (by omega)
  have hle := h (t + t) hN ⟨t, rfl⟩
  rw [ht] at hle
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  push_cast at hge hle hlt
  have : C * Real.log (t + t) / ((t : ℝ) + t) ^ 2 < (t + t) / (t * (t + t - t)) := by
    rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith [mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < t * t)]
  linarith

/-- **Refutation (literal induced-subgraph reading).** `λ₂ = 0` on every layer, which is not
`Ω(log n / n²)`. -/
theorem induced_not_bigOmega :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      c * Real.log n / (n : ℝ) ^ 2 ≤ algConn (inducedLayer n (n / 2)) := by
  rintro ⟨c, hc, N, h⟩
  have hle := h (2 * N + 2) (by omega) ⟨N + 1, by ring⟩
  rw [algConn_inducedLayer] at hle
  have hn : (2 : ℝ) ≤ ((2 * N + 2 : ℕ) : ℝ) := by
    push_cast; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have : 0 < c * Real.log ((2 * N + 2 : ℕ) : ℝ) / ((2 * N + 2 : ℕ) : ℝ) ^ 2 :=
    div_pos (mul_pos hc (Real.log_pos (by linarith))) (by positivity)
  linarith

/-- **Main theorem.** Conjecture 00000003963 fails on each reading: Johnson graph with the
Laplacian (minimum over layers, and the middle layer), Johnson graph with the normalized
Laplacian (middle layer), and the literal induced subgraph of `Q_n` (middle layer). -/
theorem conjecture_3963_false :
    (¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ k, 1 ≤ k ∧ k + 1 ≤ n ∧ algConn (johnson n k) ≤ C * Real.log n / (n : ℝ) ^ 2) ∧
    (¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      algConn (johnson n (n / 2)) ≤ C * Real.log n / (n : ℝ) ^ 2) ∧
    (¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      lambda2 (normLap_isHermitian (johnson n (n / 2))) ≤ C * Real.log n / (n : ℝ) ^ 2) ∧
    (¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      c * Real.log n / (n : ℝ) ^ 2 ≤ algConn (inducedLayer n (n / 2))) :=
  ⟨johnson_min_not_bigO, johnson_not_bigO, johnson_norm_not_bigO, induced_not_bigOmega⟩

end C3963
