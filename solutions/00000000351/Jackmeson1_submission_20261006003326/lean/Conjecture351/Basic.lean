import Mathlib

/-!
# Conjecture 00000000351 is false in dimension 3

The conjecture: for dimensions up to eight the `Dₙ` lattices are covering-optimal (they give the
thinnest lattice covering of `ℝⁿ`), with the first exception in dimension nine.  We show that in
dimension 3 the lattice spanned by `e₁`, `e₂` and `(½, ½, ½)` (the body-centred cubic lattice
`ℤ³ ∪ (ℤ³ + (½, ½, ½))`) has strictly smaller covering density than every similar copy of `D₃`.

The lattice set-up (`Dlat`, `IsSimilarCopy`, `covolume_span`, `abs_det_isometry`) is adapted from
the accepted package for conjecture 00000000238.
-/

open MeasureTheory Metric Module Submodule
open scoped Real

namespace C351

/-- Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A lattice in `ℝⁿ`: a discrete subgroup of `ℝⁿ` spanning `ℝⁿ` (a `ℤ`-lattice in Mathlib's
sense). -/
structure Lattice (n : ℕ) where
  Λ : Submodule ℤ (Rn n)
  discrete : DiscreteTopology Λ
  spans : IsZLattice ℝ Λ

/-- The covering radius of `S ⊆ ℝⁿ`: the smallest `r ≥ 0` such that the closed balls of radius `r`
centred at the points of `S` cover `ℝⁿ`, i.e. `inf {r ≥ 0 | ∀ x, ∃ l ∈ S, dist x l ≤ r}`. -/
noncomputable def coveringRadius {n : ℕ} (S : Set (Rn n)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∀ x : Rn n, ∃ l ∈ S, dist x l ≤ r}

/-- The covering density `Θ(Λ) = vol B(0, μ(Λ)) / covol(Λ)` of a lattice `Λ`, where `μ(Λ)` is the
covering radius and `covol` is Mathlib's `ZLattice.covolume` (the volume of a fundamental domain). -/
noncomputable def coveringDensity {n : ℕ} (Λ : Submodule ℤ (Rn n)) : ℝ :=
  volume.real (closedBall (0 : Rn n) (coveringRadius (Λ : Set (Rn n)))) / ZLattice.covolume Λ

/-- The root lattice `Dₙ = {x ∈ ℤⁿ : x₁ + ⋯ + xₙ is even}`. -/
def Dlat (n : ℕ) : Submodule ℤ (Rn n) where
  carrier := {x | ∃ z : Fin n → ℤ, (∀ i, x i = z i) ∧ Even (∑ i, z i)}
  add_mem' := by
    rintro x y ⟨z, hz, he⟩ ⟨w, hw, hf⟩
    exact ⟨z + w, fun i => by simp [hz, hw], by simpa [Finset.sum_add_distrib] using he.add hf⟩
  zero_mem' := ⟨0, fun i => by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨z, hz, he⟩
    exact ⟨c • z, fun i => by simp [hz], by simpa [Finset.mul_sum] using he.mul_left c⟩

/-- `Λ` is a similar copy of `M`: `Λ = {c • φ x : x ∈ M}` for a scalar `c ≠ 0` and a linear
isometry `φ` of `ℝⁿ`. -/
def IsSimilarCopy {n : ℕ} (M Λ : Submodule ℤ (Rn n)) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∃ φ : Rn n ≃ₗᵢ[ℝ] Rn n,
    (Λ : Set (Rn n)) = (fun x => c • φ x) '' (M : Set (Rn n))

/-- "`Dₙ` is covering-optimal": some similar copy of `Dₙ` has covering density at most that of
every lattice in `ℝⁿ` (it gives the thinnest lattice covering). -/
def DCoveringOptimal (n : ℕ) : Prop :=
  ∃ Q : Submodule ℤ (Rn n), IsSimilarCopy (Dlat n) Q ∧
    ∀ L : Lattice n, coveringDensity Q ≤ coveringDensity L.Λ

/-! ### Generalities on the covering radius -/

lemma coveringRadius_le {n : ℕ} {S : Set (Rn n)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x, ∃ l ∈ S, dist x l ≤ r) : coveringRadius S ≤ r :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨hr, h⟩

lemma coveringRadius_nonneg {n : ℕ} (S : Set (Rn n)) : 0 ≤ coveringRadius S :=
  Real.sInf_nonneg (fun _ hs => hs.1)

/-- If balls of some radius `R` centred at `S` cover, and `p` is at distance `≥ r` from every
point of `S`, then the covering radius is at least `r`. -/
lemma le_coveringRadius {n : ℕ} {S : Set (Rn n)} {R r : ℝ} (hR : 0 ≤ R)
    (hcov : ∀ x, ∃ l ∈ S, dist x l ≤ R) (p : Rn n) (hp : ∀ l ∈ S, r ≤ dist p l) :
    r ≤ coveringRadius S :=
  le_csInf ⟨R, hR, hcov⟩ (fun _ hs => by
    obtain ⟨l, hl, hd⟩ := hs.2 p
    exact (hp l hl).trans hd)

lemma vol_closedBall {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall (0 : Rn 3) r) = r ^ 3 * (π * 4 / 3) := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]

lemma dist_sq3 (x y : Rn 3) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]

lemma dist_le_of_sq {x y : Rn 3} {r : ℝ} (hr : 0 ≤ r) (h : dist x y ^ 2 ≤ r ^ 2) :
    dist x y ≤ r := by
  nlinarith [dist_nonneg (x := x) (y := y)]

/-! ### Explicit bases and covolumes -/

/-- The vector of `ℝ³` whose coordinates are the `j`-th row of the real matrix `A`. -/
noncomputable def vec (A : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : Rn 3 :=
  WithLp.toLp 2 (fun i => A j i)

/-- The standard basis of `ℝ³`. -/
noncomputable def stdB : Basis (Fin 3) ℝ (Rn 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

lemma stdB_det_vec (A : Matrix (Fin 3) (Fin 3) ℝ) : stdB.det (vec A) = A.det := by
  rw [Basis.det_apply]
  have : stdB.toMatrix (vec A) = A.transpose := by
    ext i j
    simp [Basis.toMatrix_apply, stdB, vec]
  rw [this, Matrix.det_transpose]

/-- The `ℝ`-basis given by a family with nonzero determinant. -/
noncomputable def basisOfDet (v : Fin 3 → Rn 3) (h : stdB.det v ≠ 0) : Basis (Fin 3) ℝ (Rn 3) :=
  Basis.mk ((stdB.is_basis_iff_det).2 (Ne.isUnit h)).1 ((stdB.is_basis_iff_det).2 (Ne.isUnit h)).2.ge

lemma coe_basisOfDet (v : Fin 3 → Rn 3) (h : stdB.det v ≠ 0) : ⇑(basisOfDet v h) = v := by
  simp [basisOfDet]

/-- The covolume of the lattice spanned by an `ℝ`-basis `b` of `ℝ³` is `|det b|`. -/
lemma covolume_span (b : Basis (Fin 3) ℝ (Rn 3)) :
    ZLattice.covolume (span ℤ (Set.range b)) = |stdB.det b| := by
  have h1 := ZLattice.covolume_eq_det_mul_measureReal (span ℤ (Set.range b)) volume
    (b.restrictScalars ℤ) stdB
  have h2 : ((↑) ∘ b.restrictScalars ℤ : Fin 3 → Rn 3) = b := by ext1 i; simp
  have h3 : volume.real (ZSpan.fundamentalDomain stdB) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped stdB volume)]
    simp [stdB, measureReal_def, (EuclideanSpace.basisFun (Fin 3) ℝ).volume_parallelepiped]
  rw [h1, h2, h3, mul_one]

/-! ### The lattice `D₃` and its similar copies -/

/-- Basis of `D₃`: `e₁ + e₃`, `e₂ + e₃`, `2 e₃`. -/
def AD : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; 0, 1, 1; 0, 0, 2]

noncomputable def vD : Fin 3 → Rn 3 := vec (AD.map (Int.cast : ℤ → ℝ))

lemma det_vD : stdB.det vD = 2 := by
  rw [vD, stdB_det_vec, Matrix.det_fin_three]
  simp [AD]

lemma Dlat_eq_span : Dlat 3 = span ℤ (Set.range vD) := by
  apply le_antisymm
  · rintro x ⟨z, hz, k, hk⟩
    rw [mem_span_range_iff_exists_fun]
    refine ⟨![z 0, z 1, k - (z 0 + z 1)], ?_⟩
    have hkR : (∑ i, (z i : ℝ)) = k + k := by exact_mod_cast hk
    simp [Fin.sum_univ_succ] at hkR
    ext i
    fin_cases i <;> (simp [Fin.sum_univ_succ, vD, vec, AD, hz]; try linarith)
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i => AD j i, fun i => by simp [vD, vec], ?_⟩
    fin_cases j <;> simp [AD, Fin.sum_univ_succ]

/-- Every point of `ℝ³` is within distance `2` of `D₃` (round to the sublattice `2ℤ³`). -/
lemma D3_covers (y : Rn 3) : ∃ m ∈ (Dlat 3 : Set (Rn 3)), dist y m ≤ 2 := by
  refine ⟨WithLp.toLp 2 (fun i => ((2 * round (y i / 2) : ℤ) : ℝ)),
    ⟨fun i => 2 * round (y i / 2), fun i => rfl, ?_⟩, ?_⟩
  · rw [← Finset.mul_sum]
    exact even_two_mul _
  · apply dist_le_of_sq (by norm_num)
    have h : ∀ i, (y i - ((2 * round (y i / 2) : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      intro i
      have h1 := abs_le.1 (abs_sub_round (y i / 2))
      push_cast
      nlinarith [h1.1, h1.2]
    rw [dist_sq3]
    nlinarith [h 0, h 1, h 2]

/-- The deep hole `(1, 0, 0)`: it is at distance `≥ 1` from every point of `D₃`. -/
lemma D3_deep_hole (m : Rn 3) (hm : m ∈ Dlat 3) :
    1 ≤ dist (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ) : Rn 3) m := by
  obtain ⟨z, hz, k, hk⟩ := hm
  simp only [Fin.sum_univ_three] at hk
  have key : (1 : ℤ) ≤ (1 - z 0) ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rcases eq_or_ne (z 1) 0 with h1 | h1
    · rcases eq_or_ne (z 2) 0 with h2 | h2
      · have h0 : 1 - z 0 ≠ 0 := by omega
        nlinarith [Int.one_le_abs h0, sq_abs (1 - z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
      · nlinarith [Int.one_le_abs h2, sq_abs (z 2), sq_nonneg (1 - z 0), sq_nonneg (z 1)]
    · nlinarith [Int.one_le_abs h1, sq_abs (z 1), sq_nonneg (1 - z 0), sq_nonneg (z 2)]
  have keyR : (1 : ℝ) ≤ (1 - z 0) ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by exact_mod_cast key
  have hd := dist_sq3 (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ) : Rn 3) m
  simp [hz] at hd
  nlinarith [dist_nonneg (x := (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ) : Rn 3)) (y := m)]

lemma abs_det_isometry (φ : Rn 3 ≃ₗᵢ[ℝ] Rn 3) :
    |LinearMap.det φ.toLinearEquiv.toLinearMap| = 1 := by
  have h := Basis.det_comp stdB φ.toLinearEquiv.toLinearMap stdB
  rw [Basis.det_self, mul_one] at h
  rw [← h]
  have e : (φ.toLinearEquiv.toLinearMap ∘ stdB) = ⇑((EuclideanSpace.basisFun (Fin 3) ℝ).map φ) := by
    ext1 i
    simp [stdB]
  rw [e]
  rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real (EuclideanSpace.basisFun (Fin 3) ℝ)
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map φ) with h' | h' <;> simp [stdB, h']

/-- A similar copy `c • φ(D₃)` has covering radius `≥ |c|` and covolume `2 |c|³`. -/
lemma similar_D3_bounds (Q : Submodule ℤ (Rn 3)) (hQ : IsSimilarCopy (Dlat 3) Q) :
    ∃ c : ℝ, c ≠ 0 ∧ |c| ≤ coveringRadius (Q : Set (Rn 3)) ∧
      ZLattice.covolume Q = |c| ^ 3 * 2 := by
  obtain ⟨c, hc, φ, hΛ⟩ := hQ
  refine ⟨c, hc, ?_, ?_⟩
  · have hd : ∀ a b : Rn 3, dist (c • φ a) (c • φ b) = |c| * dist a b := by
      intro a b
      rw [dist_smul₀, LinearIsometryEquiv.dist_map, Real.norm_eq_abs]
    rw [hΛ]
    refine le_coveringRadius (R := |c| * 2) (by positivity) ?_
      (c • φ (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ))) ?_
    · intro x
      obtain ⟨m, hm, hdm⟩ := D3_covers (φ.symm (c⁻¹ • x))
      refine ⟨c • φ m, ⟨m, hm, rfl⟩, ?_⟩
      have hx : c • φ (φ.symm (c⁻¹ • x)) = x := by
        rw [LinearIsometryEquiv.apply_symm_apply, smul_inv_smul₀ hc]
      calc dist x (c • φ m) = dist (c • φ (φ.symm (c⁻¹ • x))) (c • φ m) := by rw [hx]
        _ = |c| * dist (φ.symm (c⁻¹ • x)) m := hd _ _
        _ ≤ |c| * 2 := mul_le_mul_of_nonneg_left hdm (abs_nonneg c)
    · rintro l ⟨m, hm, rfl⟩
      show |c| ≤ dist (c • φ _) (c • φ m)
      rw [hd]
      have := D3_deep_hole m hm
      nlinarith [abs_nonneg c]
  · set f : Rn 3 →ₗ[ℝ] Rn 3 := c • φ.toLinearEquiv.toLinearMap with hf
    have hdet : stdB.det (f ∘ vD) = c ^ 3 * LinearMap.det φ.toLinearEquiv.toLinearMap * 2 := by
      rw [Basis.det_comp, hf, LinearMap.det_smul, finrank_euclideanSpace_fin, det_vD]
    have hdet0 : stdB.det (f ∘ vD) ≠ 0 := by
      rw [hdet]
      have h1 := abs_det_isometry φ
      have h2 : LinearMap.det φ.toLinearEquiv.toLinearMap ≠ 0 := by
        intro h0; rw [h0] at h1; simp at h1
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) h2) two_ne_zero
    have hQb : Q = span ℤ (Set.range (basisOfDet _ hdet0)) := by
      apply SetLike.coe_injective
      have e : (⇑f '' Set.range vD) = ⇑(f.restrictScalars ℤ) '' Set.range vD := rfl
      rw [hΛ, coe_basisOfDet, Set.range_comp, e, Submodule.span_image, ← Dlat_eq_span,
        Submodule.map_coe]
      rfl
    rw [hQb, covolume_span, coe_basisOfDet, hdet, abs_mul, abs_mul, abs_det_isometry, abs_pow]
    norm_num

/-- Every similar copy of `D₃` has covering density at least `2π/3`. -/
theorem coveringDensity_similar_D3_ge (Q : Submodule ℤ (Rn 3)) (hQ : IsSimilarCopy (Dlat 3) Q) :
    2 * π / 3 ≤ coveringDensity Q := by
  obtain ⟨c, hc, hρ, hcov⟩ := similar_D3_bounds Q hQ
  have hc0 : 0 < |c| := abs_pos.2 hc
  have hρ0 := coveringRadius_nonneg (Q : Set (Rn 3))
  rw [coveringDensity, vol_closedBall hρ0, hcov, le_div_iff₀ (by positivity)]
  have hp : |c| ^ 3 ≤ coveringRadius (Q : Set (Rn 3)) ^ 3 := pow_le_pow_left₀ hc0.le hρ 3
  nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ π * 4 / 3)]

/-! ### The body-centred cubic lattice -/

/-- Basis of the body-centred cubic lattice: `e₁`, `e₂`, `(½, ½, ½)`. -/
noncomputable def AB : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 1 / 2, 1 / 2, 1 / 2]

lemma det_AB : AB.det = 1 / 2 := by
  rw [Matrix.det_fin_three]
  simp [AB]

noncomputable def bB : Basis (Fin 3) ℝ (Rn 3) :=
  basisOfDet (vec AB) (by rw [stdB_det_vec, det_AB]; norm_num)

lemma coe_bB : ⇑bB = vec AB := coe_basisOfDet _ _

/-- The body-centred cubic lattice, as the `ℤ`-span of `e₁`, `e₂`, `(½, ½, ½)`. -/
noncomputable def bcc : Lattice 3 where
  Λ := span ℤ (Set.range bB)
  discrete := inferInstance
  spans := inferInstance

lemma covolume_bcc : ZLattice.covolume bcc.Λ = 1 / 2 := by
  show ZLattice.covolume (span ℤ (Set.range bB)) = 1 / 2
  rw [covolume_span, coe_bB, stdB_det_vec, det_AB]
  norm_num

/-- `z + (e/2)(1,1,1) ∈ bcc` for all `z ∈ ℤ³`, `e ∈ ℤ`. -/
lemma mem_bcc (z : Fin 3 → ℤ) (e : ℤ) :
    (WithLp.toLp 2 (fun i => (z i : ℝ) + (e : ℝ) / 2) : Rn 3) ∈ bcc.Λ := by
  show _ ∈ span ℤ (Set.range bB)
  rw [mem_span_range_iff_exists_fun]
  refine ⟨![z 0 - z 2, z 1 - z 2, 2 * z 2 + e], ?_⟩
  rw [coe_bB]
  ext i
  fin_cases i <;> (simp [Fin.sum_univ_succ, vec, AB]; ring)

/-- `bcc = {z + (e/2)(1,1,1) : z ∈ ℤ³, e ∈ ℤ}` (splitting e into even and odd cases gives
`ℤ³ ∪ (ℤ³ + (½, ½, ½))`; that two-coset form is not separately formalized). -/
lemma mem_bcc_iff (x : Rn 3) : x ∈ bcc.Λ ↔
    ∃ z : Fin 3 → ℤ, ∃ e : ℤ, x = WithLp.toLp 2 (fun i => (z i : ℝ) + (e : ℝ) / 2) := by
  refine ⟨fun hx => ?_, fun ⟨z, e, hx⟩ => hx ▸ mem_bcc z e⟩
  change x ∈ span ℤ (Set.range bB) at hx
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨![c 0, c 1, 0], c 2, ?_⟩
  rw [coe_bB]
  ext i
  fin_cases i <;> (simp [Fin.sum_univ_succ, vec, AB]; ring)

lemma round_pair (y : ℝ) : ∃ a b : ℤ, (y - a) ^ 2 + (y - (b + 1 / 2)) ^ 2 ≤ 1 / 4 := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  by_cases h : y - ⌊y⌋ ≤ 1 / 2
  · exact ⟨⌊y⌋, ⌊y⌋, by nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h)]⟩
  · replace h := not_le.1 h
    refine ⟨⌊y⌋ + 1, ⌊y⌋, ?_⟩
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 h.le) (sub_nonneg.2 h2.le)]

/-- Closed balls of radius `5/8` centred at the points of `bcc` cover `ℝ³`. -/
lemma bcc_covers (x : Rn 3) : ∃ l ∈ (bcc.Λ : Set (Rn 3)), dist x l ≤ 5 / 8 := by
  choose a b hab using fun i => round_pair (x i)
  have hA := mem_bcc a 0
  have hB := mem_bcc b 1
  have hsum : dist x (WithLp.toLp 2 (fun i => (a i : ℝ) + ((0 : ℤ) : ℝ) / 2)) ^ 2 +
      dist x (WithLp.toLp 2 (fun i => (b i : ℝ) + ((1 : ℤ) : ℝ) / 2)) ^ 2 ≤ 3 / 4 := by
    rw [dist_sq3, dist_sq3]
    simp only [Int.cast_zero, Int.cast_one, zero_div, add_zero]
    nlinarith [hab 0, hab 1, hab 2]
  by_cases h : dist x (WithLp.toLp 2 (fun i => (a i : ℝ) + ((0 : ℤ) : ℝ) / 2)) ^ 2 ≤ 3 / 8
  · exact ⟨_, hA, dist_le_of_sq (by norm_num) (by nlinarith)⟩
  · exact ⟨_, hB, dist_le_of_sq (by norm_num) (by nlinarith)⟩

/-- The covering density of `bcc` is at most `125π/192`. -/
theorem coveringDensity_bcc_le : coveringDensity bcc.Λ ≤ 125 * π / 192 := by
  have hρ := coveringRadius_le (by norm_num) bcc_covers
  have hρ0 := coveringRadius_nonneg (bcc.Λ : Set (Rn 3))
  rw [coveringDensity, vol_closedBall hρ0, covolume_bcc, div_le_iff₀ (by norm_num)]
  have hp := pow_le_pow_left₀ hρ0 hρ 3
  nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ π * 4 / 3)]

/-! ### Main results -/

/-- The body-centred cubic lattice has strictly smaller covering density than every similar copy
of `D₃`. -/
theorem coveringDensity_bcc_lt_similar_D3 (Q : Submodule ℤ (Rn 3))
    (hQ : IsSimilarCopy (Dlat 3) Q) : coveringDensity bcc.Λ < coveringDensity Q := by
  have h1 := coveringDensity_bcc_le
  have h2 := coveringDensity_similar_D3_ge Q hQ
  linarith [Real.pi_pos]

/-- In particular `Θ(bcc) < Θ(D₃)`. -/
theorem coveringDensity_bcc_lt_D3 : coveringDensity bcc.Λ < coveringDensity (Dlat 3) :=
  coveringDensity_bcc_lt_similar_D3 _ ⟨1, one_ne_zero, LinearIsometryEquiv.refl ℝ _, by simp⟩

/-- `D₃` is not covering-optimal: no similar copy of `D₃` gives the thinnest lattice covering
of `ℝ³`. -/
theorem not_DCoveringOptimal_three : ¬ DCoveringOptimal 3 := by
  rintro ⟨Q, hQ, hmin⟩
  exact absurd (hmin bcc) (not_le.2 (coveringDensity_bcc_lt_similar_D3 Q hQ))

/-- **Conjecture 00000000351 is false**: it is not true that the `Dₙ` lattices are
covering-optimal in every dimension `3 ≤ n ≤ 8` (dimension 3 fails). -/
theorem conjecture_351_false : ¬ ∀ n ∈ Finset.Icc 3 8, DCoveringOptimal n :=
  fun h => not_DCoveringOptimal_three (h 3 (by decide))

end C351
