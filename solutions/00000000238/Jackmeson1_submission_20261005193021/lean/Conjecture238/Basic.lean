import Mathlib

/-!
# Conjecture 00000000238 is false in dimension 7

The conjecture: the densest lattice packings (of non-overlapping unit balls) in dimensions five, six
and seven are given by the `D` lattices.  We exhibit, in dimension 7, an explicit lattice packing of
unit balls (centred at a sublattice of the Construction-A lattice of the binary `[7,3,4]` simplex
code, an integral model of `√2 E₇`; that identification is not used) that is strictly denser than
every lattice packing of unit balls whose centres form a similar copy of `D₇`.
-/

open MeasureTheory Metric Module Submodule
open scoped Pointwise

namespace C238

/-- Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A lattice packing of unit balls in `ℝⁿ`: a lattice `Λ` (a discrete subgroup of `ℝⁿ` spanning
`ℝⁿ`, i.e. a `ℤ`-lattice in Mathlib's sense) such that the open unit balls centred at distinct points
of `Λ` do not overlap. -/
structure LatticePacking (n : ℕ) where
  Λ : Submodule ℤ (Rn n)
  discrete : DiscreteTopology Λ
  spans : IsZLattice ℝ Λ
  nonoverlap : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → Disjoint (ball x 1) (ball y 1)

/-- The density of a lattice packing of unit balls: the volume of one unit ball divided by the
covolume of the lattice (the volume of a fundamental domain, Mathlib's `ZLattice.covolume`). -/
noncomputable def LatticePacking.density {n : ℕ} (P : LatticePacking n) : ℝ :=
  volume.real (ball (0 : Rn n) 1) / ZLattice.covolume P.Λ

/-- The density is the fraction of a fundamental cell filled by the balls: for every fundamental
domain `F` of the lattice, `vol((⋃_{x ∈ Λ} B(x,1)) ∩ F) / vol(F) = P.density`. -/
theorem LatticePacking.filled_fraction {n : ℕ} (P : LatticePacking n) {F : Set (Rn n)}
    (hF : IsAddFundamentalDomain P.Λ F volume) :
    volume.real ((⋃ x : P.Λ, ball (x : Rn n) 1) ∩ F) / volume.real F = P.density := by
  have := P.discrete
  have := P.spans
  have : VAddInvariantMeasure P.Λ (Rn n) volume :=
    (inferInstance : VAddInvariantMeasure P.Λ.toAddSubgroup (Rn n) volume)
  rw [LatticePacking.density, ZLattice.covolume_eq_measure_fundamentalDomain P.Λ volume hF]
  congr 1
  simp only [measureReal_def]
  congr 1
  have hd : Pairwise (Function.onFun (AEDisjoint volume) fun g : P.Λ => ball (g : Rn n) 1 ∩ F) :=
    fun g g' hgg' => ((P.nonoverlap g g.2 g' g'.2 (Subtype.coe_injective.ne hgg')).mono
      Set.inter_subset_left Set.inter_subset_left).aedisjoint
  have hm : ∀ g : P.Λ, NullMeasurableSet (ball (g : Rn n) 1 ∩ F) volume :=
    fun g => measurableSet_ball.nullMeasurableSet.inter hF.nullMeasurableSet
  rw [Set.iUnion_inter, measure_iUnion₀ hd hm, hF.measure_eq_tsum (ball 0 1)]
  congr 1
  funext g
  congr 1
  rw [show (g +ᵥ ball (0 : Rn n) 1) = ((g : Rn n) +ᵥ ball (0 : Rn n) 1) from rfl, vadd_ball_zero]

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

/-- "The densest lattice packing of unit balls in `ℝⁿ` is given by the `D` lattice": some lattice
packing of unit balls whose centres form a similar copy of `Dₙ` is at least as dense as every
lattice packing of unit balls. -/
def DLatticeIsDensest (n : ℕ) : Prop :=
  ∃ Q : LatticePacking n, IsSimilarCopy (Dlat n) Q.Λ ∧ ∀ P : LatticePacking n, P.density ≤ Q.density

/-! ### Explicit bases and their determinants -/

/-- The vector of `ℝ⁷` whose coordinates are the `j`-th row of the integer matrix `A`. -/
def vec (A : Matrix (Fin 7) (Fin 7) ℤ) (j : Fin 7) : Rn 7 := WithLp.toLp 2 (fun i => (A j i : ℝ))

/-- The standard basis of `ℝ⁷`. -/
noncomputable def stdB : Basis (Fin 7) ℝ (Rn 7) := (EuclideanSpace.basisFun (Fin 7) ℝ).toBasis

lemma stdB_det_vec (A : Matrix (Fin 7) (Fin 7) ℤ) : stdB.det (vec A) = (A.det : ℝ) := by
  rw [Basis.det_apply]
  have : stdB.toMatrix (vec A) = (A.map (Int.cast : ℤ → ℝ)).transpose := by
    ext i j
    simp [Basis.toMatrix_apply, stdB, vec]
  rw [this, Matrix.det_transpose, Int.cast_det]

/-- The `ℝ`-basis given by a family with nonzero determinant. -/
noncomputable def basisOfDet (v : Fin 7 → Rn 7) (h : stdB.det v ≠ 0) : Basis (Fin 7) ℝ (Rn 7) :=
  Basis.mk ((stdB.is_basis_iff_det).2 (Ne.isUnit h)).1 ((stdB.is_basis_iff_det).2 (Ne.isUnit h)).2.ge

lemma coe_basisOfDet (v : Fin 7 → Rn 7) (h : stdB.det v ≠ 0) : ⇑(basisOfDet v h) = v := by
  simp [basisOfDet]

/-- The covolume of the lattice spanned by an `ℝ`-basis `b` of `ℝ⁷` is `|det b|`. -/
lemma covolume_span (b : Basis (Fin 7) ℝ (Rn 7)) :
    ZLattice.covolume (span ℤ (Set.range b)) = |stdB.det b| := by
  have h1 := ZLattice.covolume_eq_det_mul_measureReal (span ℤ (Set.range b)) volume
    (b.restrictScalars ℤ) stdB
  have h2 : ((↑) ∘ b.restrictScalars ℤ : Fin 7 → Rn 7) = b := by ext1 i; simp
  have h3 : volume.real (ZSpan.fundamentalDomain stdB) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped stdB volume)]
    simp [stdB, measureReal_def, (EuclideanSpace.basisFun (Fin 7) ℝ).volume_parallelepiped]
  rw [h1, h2, h3, mul_one]

/-- Basis of `D₇`: `eⱼ + e₇` for `j ≤ 6` and `2 e₇`. -/
def AD : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0, 2]

/-- Basis of the Construction-A lattice: the three generators of the simplex code, and `2 eᵢ`. -/
def AL : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1, 0, 0, 0, 1, 1, 1;
     0, 1, 0, 1, 0, 1, 1;
     0, 0, 1, 1, 1, 0, 1;
     0, 0, 0, 2, 0, 0, 0;
     0, 0, 0, 0, 2, 0, 0;
     0, 0, 0, 0, 0, 2, 0;
     0, 0, 0, 0, 0, 0, 2]

lemma det_AD : AD.det = 2 := by
  have h : ∀ i j : Fin 7, j < i → AD i j = 0 := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [AD]
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h i j hij)]
  simp [AD, Fin.prod_univ_succ]

lemma det_AL : AL.det = 16 := by
  have h : ∀ i j : Fin 7, j < i → AL i j = 0 := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [AL]
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h i j hij)]
  simp [AL, Fin.prod_univ_succ]

noncomputable def bL : Basis (Fin 7) ℝ (Rn 7) :=
  basisOfDet (vec AL) (by rw [stdB_det_vec, det_AL]; norm_num)

lemma coe_bL : ⇑bL = vec AL := coe_basisOfDet _ _

/-! ### The Construction-A lattice of the `[7,3,4]` simplex code -/

/-- Generator matrix of the binary `[7,3,4]` simplex code. -/
def G : Fin 3 → Fin 7 → ZMod 2 := ![![1, 0, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 1, 0, 1]]

/-- The codeword with message `a`. -/
def cw (a : Fin 3 → ZMod 2) (i : Fin 7) : ZMod 2 := ∑ k, a k * G k i

/-- Every nonzero codeword has weight at least 4. -/
lemma weight_ge (a : Fin 3 → ZMod 2) (ha : a ≠ 0) :
    4 ≤ (Finset.univ.filter fun i => cw a i ≠ 0).card := by
  have e : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  rw [e] at ha ⊢
  generalize a 0 = x, a 1 = y, a 2 = z at ha ⊢
  revert x y z
  decide

/-- Construction A: `{x ∈ ℤ⁷ : x mod 2 is a codeword}`. -/
def E7A : Submodule ℤ (Rn 7) where
  carrier := {x | ∃ z : Fin 7 → ℤ, (∀ i, x i = z i) ∧ ∃ a : Fin 3 → ZMod 2, ∀ i, (z i : ZMod 2) = cw a i}
  add_mem' := by
    rintro x y ⟨z, hz, a, ha⟩ ⟨w, hw, b, hb⟩
    refine ⟨z + w, fun i => by simp [hz, hw], a + b, fun i => ?_⟩
    simp [ha, hb, cw, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun i => by simp, 0, fun i => by simp [cw]⟩
  smul_mem' := by
    rintro c x ⟨z, hz, a, ha⟩
    refine ⟨c • z, fun i => by simp [hz], (c : ZMod 2) • a, fun i => ?_⟩
    simp [ha, cw, Finset.mul_sum, mul_assoc]

lemma sum_sq_ge (z : Fin 7 → ℤ) (a : Fin 3 → ZMod 2) (ha : ∀ i, (z i : ZMod 2) = cw a i)
    (hz : z ≠ 0) : 4 ≤ ∑ i, z i ^ 2 := by
  by_cases ha0 : a = 0
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by by_contra h; push Not at h; exact hz (funext h)
    have h2 : (2 : ℤ) ∣ z i := by
      have := ha i
      rw [ha0] at this
      simp [cw] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (z i) 2).1 this
    obtain ⟨k, hk⟩ := h2
    have hk0 : k ≠ 0 := by rintro rfl; exact hi (by simpa using hk)
    have h4 : 4 ≤ z i ^ 2 := by
      rw [hk]
      nlinarith [Int.one_le_abs hk0, sq_abs k, abs_nonneg k]
    calc 4 ≤ z i ^ 2 := h4
      _ ≤ ∑ j, z j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  · set S := Finset.univ.filter fun i => cw a i ≠ 0
    have hS : 4 ≤ S.card := weight_ge a ha0
    have hodd : ∀ i ∈ S, (1 : ℤ) ≤ z i ^ 2 := by
      intro i hi
      have hne : z i ≠ 0 := by
        intro h0
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        apply hi
        rw [← ha i, h0]
        simp
      nlinarith [Int.one_le_abs hne, sq_abs (z i), abs_nonneg (z i)]
    calc (4 : ℤ) ≤ S.card := by exact_mod_cast hS
      _ = ∑ i ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ S, z i ^ 2 := Finset.sum_le_sum hodd
      _ ≤ ∑ i, z i ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)

lemma norm_sq_eq (x : Rn 7) (z : Fin 7 → ℤ) (hz : ∀ i, x i = z i) :
    ‖x‖ ^ 2 = ((∑ i, z i ^ 2 : ℤ) : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  simp [hz, Real.norm_eq_abs, sq_abs]

/-- Every nonzero vector of the Construction-A lattice has length at least `2`. -/
lemma E7A_norm (x : Rn 7) (hx : x ∈ E7A) (h0 : x ≠ 0) : 2 ≤ ‖x‖ := by
  obtain ⟨z, hz, a, ha⟩ := hx
  have hz0 : z ≠ 0 := by rintro rfl; apply h0; ext i; simp [hz]
  have h4 := sum_sq_ge z a ha hz0
  have : (4 : ℝ) ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq x z hz]
    exact_mod_cast h4
  nlinarith [norm_nonneg x]

lemma span_le_E7A : span ℤ (Set.range bL) ≤ E7A := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [coe_bL]
  refine ⟨fun i => AL j i, fun i => rfl, ?_⟩
  fin_cases j
  · exact ⟨![1, 0, 0], fun i => by fin_cases i <;> simp [AL, cw, G, Fin.sum_univ_succ]⟩
  · exact ⟨![0, 1, 0], fun i => by fin_cases i <;> simp [AL, cw, G, Fin.sum_univ_succ]⟩
  · exact ⟨![0, 0, 1], fun i => by fin_cases i <;> simp [AL, cw, G, Fin.sum_univ_succ]⟩
  all_goals exact ⟨0, fun i => by fin_cases i <;> (simp [AL, cw]; try decide)⟩

/-- The lattice packing of unit balls centred at the lattice spanned by the rows of `AL` (a
sublattice of `E7A`, which is all that is used). -/
noncomputable def PE7 : LatticePacking 7 where
  Λ := span ℤ (Set.range bL)
  discrete := inferInstance
  spans := inferInstance
  nonoverlap := by
    intro x hx y hy hxy
    rw [disjoint_ball_ball_iff one_pos one_pos, dist_eq_norm]
    norm_num
    exact E7A_norm (x - y) (span_le_E7A (sub_mem hx hy)) (sub_ne_zero.2 hxy)

lemma PE7_density : PE7.density = volume.real (ball (0 : Rn 7) 1) / 16 := by
  simp only [LatticePacking.density, PE7]
  rw [covolume_span, coe_bL, stdB_det_vec, det_AL]
  norm_num

/-! ### Similar copies of `D₇` -/

lemma Dlat_eq_span : Dlat 7 = span ℤ (Set.range (vec AD)) := by
  apply le_antisymm
  · rintro x ⟨z, hz, k, hk⟩
    rw [mem_span_range_iff_exists_fun]
    refine ⟨![z 0, z 1, z 2, z 3, z 4, z 5, k - (z 0 + z 1 + z 2 + z 3 + z 4 + z 5)], ?_⟩
    have hkR : (∑ i, (z i : ℝ)) = k + k := by exact_mod_cast hk
    simp [Fin.sum_univ_succ] at hkR
    ext i
    fin_cases i <;> (simp [Fin.sum_univ_succ, vec, AD, hz]; try linarith)
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i => AD j i, fun i => rfl, ?_⟩
    fin_cases j <;> simp [AD, Fin.sum_univ_succ]

lemma norm_vec_AD0 : ‖vec AD 0‖ = √2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
    EuclideanSpace.norm_sq_eq]
  simp [vec, AD, Fin.sum_univ_succ]
  norm_num

lemma abs_det_isometry (φ : Rn 7 ≃ₗᵢ[ℝ] Rn 7) :
    |LinearMap.det φ.toLinearEquiv.toLinearMap| = 1 := by
  have h := Basis.det_comp stdB φ.toLinearEquiv.toLinearMap stdB
  rw [Basis.det_self, mul_one] at h
  rw [← h]
  have e : (φ.toLinearEquiv.toLinearMap ∘ stdB) = ⇑((EuclideanSpace.basisFun (Fin 7) ℝ).map φ) := by
    ext1 i
    simp [stdB]
  rw [e]
  rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real (EuclideanSpace.basisFun (Fin 7) ℝ)
    ((EuclideanSpace.basisFun (Fin 7) ℝ).map φ) with h' | h' <;> simp [stdB, h']

/-- Every lattice packing of unit balls whose centres form a similar copy of `D₇` is strictly less
dense than the packing `PE7`. -/
theorem similar_D7_density_lt (Q : LatticePacking 7) (hQ : IsSimilarCopy (Dlat 7) Q.Λ) :
    Q.density < PE7.density := by
  obtain ⟨c, hc, φ, hΛ⟩ := hQ
  set f : Rn 7 →ₗ[ℝ] Rn 7 := c • φ.toLinearEquiv.toLinearMap with hf
  have hdet : stdB.det (f ∘ vec AD) = c ^ 7 * LinearMap.det φ.toLinearEquiv.toLinearMap * 2 := by
    rw [Basis.det_comp, hf, LinearMap.det_smul, finrank_euclideanSpace_fin, stdB_det_vec, det_AD]
    push_cast
    ring
  have hdet0 : stdB.det (f ∘ vec AD) ≠ 0 := by
    rw [hdet]
    have h1 := abs_det_isometry φ
    have h2 : LinearMap.det φ.toLinearEquiv.toLinearMap ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) h2) two_ne_zero
  have hQb : Q.Λ = span ℤ (Set.range (basisOfDet _ hdet0)) := by
    apply SetLike.coe_injective
    have e : (⇑f '' Set.range (vec AD)) = ⇑(f.restrictScalars ℤ) '' Set.range (vec AD) := rfl
    rw [hΛ, coe_basisOfDet, Set.range_comp, e, Submodule.span_image, ← Dlat_eq_span,
      Submodule.map_coe]
    rfl
  have hcov : ZLattice.covolume Q.Λ = |c| ^ 7 * 2 := by
    rw [hQb, covolume_span, coe_basisOfDet, hdet, abs_mul, abs_mul, abs_det_isometry, abs_pow]
    norm_num
  have hv0 : vec AD 0 ∈ Dlat 7 := by rw [Dlat_eq_span]; exact subset_span ⟨0, rfl⟩
  have hx : c • φ (vec AD 0) ∈ Q.Λ := by rw [← SetLike.mem_coe, hΛ]; exact ⟨_, hv0, rfl⟩
  have hnorm : ‖c • φ (vec AD 0)‖ = |c| * √2 := by
    rw [norm_smul, LinearIsometryEquiv.norm_map, norm_vec_AD0, Real.norm_eq_abs]
  have hs : (0 : ℝ) < √2 := by positivity
  have hne : c • φ (vec AD 0) ≠ 0 := by
    intro h
    have h' := congrArg norm h
    rw [hnorm, norm_zero] at h'
    exact hc (abs_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hs.ne'))
  have hd := Q.nonoverlap _ hx 0 (zero_mem _) hne
  rw [disjoint_ball_ball_iff one_pos one_pos, dist_zero_right, hnorm] at hd
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc2 : √2 ≤ |c| := by nlinarith [abs_nonneg c]
  have hpow : √2 ^ 7 ≤ |c| ^ 7 := pow_le_pow_left₀ hs.le hc2 7
  have h7 : √2 ^ 7 = 8 * √2 := by
    rw [show √2 ^ 7 = (√2 * √2) ^ 3 * √2 by ring, hss]; norm_num
  have hs1 : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hV : 0 < volume.real (ball (0 : Rn 7) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  rw [LatticePacking.density, hcov, PE7_density]
  apply div_lt_div_of_pos_left hV (by norm_num)
  nlinarith

/-- **Main theorem.** There is a lattice packing of unit balls in `ℝ⁷` that is strictly denser than
every lattice packing of unit balls whose centres form a similar copy of `D₇`. -/
theorem exists_packing_denser_than_D7 :
    ∃ P : LatticePacking 7, ∀ Q : LatticePacking 7, IsSimilarCopy (Dlat 7) Q.Λ →
      Q.density < P.density :=
  ⟨PE7, similar_D7_density_lt⟩

/-- In dimension 7 the densest lattice packing is not given by the `D` lattice. -/
theorem not_D7_densest : ¬ DLatticeIsDensest 7 := by
  rintro ⟨Q, hQ, hmax⟩
  exact absurd (hmax PE7) (not_le.2 (similar_D7_density_lt Q hQ))

/-- **Conjecture 00000000238 is false**: it is not true that in each of the dimensions 5, 6, 7 the
densest lattice packing is given by the `D` lattice. -/
theorem conjecture_238_false : ¬ ∀ n ∈ ({5, 6, 7} : Finset ℕ), DLatticeIsDensest n :=
  fun h => not_D7_densest (h 7 (by decide))

end C238
