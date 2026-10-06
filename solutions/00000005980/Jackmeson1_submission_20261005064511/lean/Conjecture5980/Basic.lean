import Mathlib

/-!
# Conjecture 00000005980 (same singular spectrum, different polar decomposition)

Statement (official): "The singular spectrum and the eigenvector statistics are two layers.
There exist two non-Hermitian models with the same singular spectrum but different eigenvector
statistics, and the separation is realized by an explicit pair with the same spectrum but
different polar decompositions."

We prove it with explicit witnesses (`conjecture_5980`). The family `F t = R(t) S R(t)ᵀ`
conjugates the non-normal seed `S = [[7,12],[0,-2]]` (eigenvalues `7, -2`, singular values
`14, 1`) by rotations. Model A is the fair law on `{F 0, F 1}` and model B is the fair law on
`{F (1/2), F (-1/2)}`. All four matrices are non-symmetric, with the same singular values
(Mathlib's `LinearMap.singularValues`) and the same characteristic polynomial. The intrinsic
eigenvector statistic `‖proj_{E_7} e₀‖²` has law `½δ₁ + ½δ₀` under A and `δ_{9/25}` under B.
The explicit pair `F 0 ∈ supp A`, `F (1/2) ∈ supp B` has equal singular values and spectra, and
the orthogonal factors differ and the positive factors differ for *every* polar decomposition
of each.

The rotation family, the eigenvector statistic and the two-point ensembles are adapted from the
accepted solution of 00000005960 (C0ldSmi1e, GPL-3.0), ported to the current Mathlib.
-/

noncomputable section
open Matrix Polynomial MeasureTheory
open scoped ENNReal MatrixOrder

namespace C5980

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Rotations (from 00000005960) -/

def cosine (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
def sine (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
def rotation (t : ℝ) : Mat2 := !![cosine t, -sine t; sine t, cosine t]

theorem cosine_sq_add_sine_sq (t : ℝ) : cosine t ^ 2 + sine t ^ 2 = 1 := by
  have : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold cosine sine
  field_simp
  ring

theorem transpose_rotation_mul_rotation (t : ℝ) : (rotation t)ᵀ * rotation t = 1 := by
  have h := cosine_sq_add_sine_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith only [h]

theorem rotation_mul_transpose_rotation (t : ℝ) : rotation t * (rotation t)ᵀ = 1 := by
  have h := cosine_sq_add_sine_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith only [h]

theorem rotation_cancel (t : ℝ) (X : Mat2) : (rotation t)ᵀ * (rotation t * X) = X := by
  rw [← Matrix.mul_assoc, transpose_rotation_mul_rotation, Matrix.one_mul]

/-! ## The non-normal seed and the family -/

/-- The seed: eigenvalues `7, -2`, singular values `14, 1`. -/
def seed : Mat2 := !![7, 12; 0, -2]

/-- The rotated family `F t = R(t) S R(t)ᵀ`. -/
def family (t : ℝ) : Mat2 := rotation t * seed * (rotation t)ᵀ

theorem family_explicit (t : ℝ) : family t =
    !![7 * cosine t ^ 2 - 12 * cosine t * sine t - 2 * sine t ^ 2,
        12 * cosine t ^ 2 + 9 * cosine t * sine t;
       9 * cosine t * sine t - 12 * sine t ^ 2,
        7 * sine t ^ 2 + 12 * cosine t * sine t - 2 * cosine t ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [family, rotation, seed, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Every member of the family is non-Hermitian (non-symmetric). -/
theorem family_not_isHermitian (t : ℝ) : ¬ (family t).IsHermitian := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [family_explicit, conjTranspose_apply] at h01
  nlinarith [cosine_sq_add_sine_sq t]

theorem charpoly_seed : seed.charpoly = (X - C (7 : ℝ)) * (X - C (-2 : ℝ)) := by
  rw [charpoly_fin_two]
  simp [seed, trace_fin_two, det_fin_two]
  ring

/-- Conjugation does not change the characteristic polynomial (eigenvalues with multiplicity). -/
theorem charpoly_conj (t : ℝ) (N : Mat2) :
    (rotation t * N * (rotation t)ᵀ).charpoly = N.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, transpose_rotation_mul_rotation, Matrix.one_mul]

theorem charpoly_family (t : ℝ) : (family t).charpoly = (X - C (7 : ℝ)) * (X - C (-2 : ℝ)) := by
  rw [family, charpoly_conj, charpoly_seed]

theorem spectrum_family (t : ℝ) : spectrum ℝ (family t) = {7, -2} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_family]
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg]

theorem gram_family (t : ℝ) :
    (family t)ᵀ * family t = rotation t * (seedᵀ * seed) * (rotation t)ᵀ := by
  simp only [family, transpose_mul, transpose_transpose, Matrix.mul_assoc, rotation_cancel]

/-! ## Singular values (Mathlib's `LinearMap.singularValues`) -/

/-- Singular values of a matrix: those of its Euclidean operator, in decreasing order. -/
def singularValues (A : Mat2) : ℕ →₀ ℝ := (toEuclideanLin A).singularValues

theorem gram_eq (A : Mat2) :
    (toEuclideanLin A).adjoint ∘ₗ toEuclideanLin A = toEuclideanLin (Aᵀ * A) := by
  rw [← toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_eq_transpose_of_trivial]
  exact (toLpLin_mul_same _ _ _).symm

theorem charpoly_toEuclideanLin (N : Mat2) : (toEuclideanLin N).charpoly = N.charpoly := by
  rw [toEuclideanLin_eq_toLin_orthonormal, charpoly_toLin]

theorem finrank_plane : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin

theorem singularValues_eq_sqrt (A : Mat2) {i : ℕ} (hi : i < 2) : singularValues A i =
    √((toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues finrank_plane ⟨i, hi⟩) :=
  LinearMap.singularValues_of_lt _ finrank_plane hi

theorem singularValues_eq_of_gram {A B : Mat2} (h : (Aᵀ * A).charpoly = (Bᵀ * B).charpoly) :
    singularValues A = singularValues B := by
  have he : (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues finrank_plane =
      (toEuclideanLin B).isSymmetric_adjoint_comp_self.eigenvalues finrank_plane := by
    rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff, gram_eq, gram_eq,
      charpoly_toEuclideanLin, charpoly_toEuclideanLin, h]
  ext i
  by_cases hi : i < 2
  · rw [singularValues_eq_sqrt A hi, singularValues_eq_sqrt B hi, he]
  · rw [singularValues, singularValues, LinearMap.singularValues_of_finrank_le _ (by
      rw [finrank_plane]; omega), LinearMap.singularValues_of_finrank_le _ (by
      rw [finrank_plane]; omega)]

/-- The whole family has the singular values of the seed. -/
theorem singularValues_family (t : ℝ) : singularValues (family t) = singularValues seed := by
  apply singularValues_eq_of_gram
  rw [gram_family, charpoly_conj]

/-- The singular values of the seed are `14, 1` (and `0` beyond the dimension). -/
theorem singularValues_seed :
    singularValues seed 0 = 14 ∧ singularValues seed 1 = 1 ∧
      ∀ i, 2 ≤ i → singularValues seed i = 0 := by
  have hT := (toEuclideanLin seed).isSymmetric_adjoint_comp_self
  have htr : (seedᵀ * seed).trace = 197 := by
    simp [seed, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  have hdt : (seedᵀ * seed).det = 196 := by
    simp [seed, det_fin_two]; norm_num
  have hchar : (LinearMap.adjoint (toEuclideanLin seed) ∘ₗ toEuclideanLin seed).charpoly =
      (X - C (196 : ℝ)) * (X - C 1) := by
    rw [gram_eq, charpoly_toEuclideanLin, charpoly_fin_two, htr, hdt,
      show (C 197 : ℝ[X]) = C 196 + 1 by rw [← C_1, ← C_add]; norm_num, C_1]
    ring
  have hsort := hT.sort_roots_charpoly_eq_eigenvalues finrank_plane
  rw [hchar, roots_mul (mul_ne_zero (X_sub_C_ne_zero 196) (X_sub_C_ne_zero 1)),
    roots_X_sub_C, roots_X_sub_C] at hsort
  have hl : List.ofFn (hT.eigenvalues finrank_plane) = [196, 1] := by
    rw [← hsort]
    apply List.Perm.eq_of_pairwise' (r := fun x1 x2 : ℝ => x1 ≥ x2) (Multiset.pairwise_sort _ _)
      (by simp)
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq]; simp; rfl
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero] at hl
  simp only [List.cons.injEq] at hl
  refine ⟨?_, ?_, fun i hi => LinearMap.singularValues_of_finrank_le _ (by
    rw [finrank_plane]; exact hi)⟩
  · rw [singularValues_eq_sqrt seed (by norm_num)]
    have : (hT.eigenvalues finrank_plane ⟨0, by norm_num⟩) = 196 := hl.1
    rw [this, show (196 : ℝ) = 14 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · rw [singularValues_eq_sqrt seed (by norm_num)]
    have : (hT.eigenvalues finrank_plane ⟨1, by norm_num⟩) = 1 := hl.2.1
    rw [this, Real.sqrt_one]

/-! ## Eigenvector statistic (from 00000005960, eigenvalue `7`) -/

def eigenspaceSeven (A : Mat2) : Submodule ℝ Plane :=
  Module.End.eigenspace (toEuclideanLin A) 7

def firstAxis : Plane := WithLp.toLp 2 ![1, 0]
def firstVector (t : ℝ) : Plane := WithLp.toLp 2 ![cosine t, sine t]

/-- Intrinsic, sign-free eigenvector statistic: squared length of the orthogonal projection of
`e₀` onto the eigenvalue-`7` eigenspace. -/
def statistic (A : Mat2) : ℝ := ‖(eigenspaceSeven A).starProjection firstAxis‖ ^ 2

theorem firstVector_norm (t : ℝ) : ‖firstVector t‖ = 1 := by
  have h : ‖firstVector t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [firstVector, Fin.sum_univ_two, Real.norm_eq_abs] using cosine_sq_add_sine_sq t
  nlinarith [norm_nonneg (firstVector t)]

theorem firstVector_mem (t : ℝ) : firstVector t ∈ eigenspaceSeven (family t) := by
  have h := cosine_sq_add_sine_sq t
  rw [eigenspaceSeven, Module.End.mem_eigenspace_iff]
  ext i
  fin_cases i <;>
    simp [toLpLin_apply, family_explicit, firstVector]
  · linear_combination (7 * cosine t) * h
  · linear_combination (7 * sine t) * h

theorem eigenspaceSeven_family (t : ℝ) :
    eigenspaceSeven (family t) = Submodule.span ℝ {firstVector t} := by
  apply le_antisymm
  · intro w hw
    rw [Submodule.mem_span_singleton]
    refine ⟨cosine t * w 0 + sine t * w 1, ?_⟩
    have he : toEuclideanLin (family t) w = (7 : ℝ) • w :=
      Module.End.mem_eigenspace_iff.mp hw
    have h0 := congrArg (fun v : Plane => v 0) he
    have h1 := congrArg (fun v : Plane => v 1) he
    simp [toLpLin_apply, family_explicit, dotProduct, Fin.sum_univ_two] at h0 h1
    have hcs := cosine_sq_add_sine_sq t
    have hu : -sine t * w 0 + cosine t * w 1 = 0 := by
      linear_combination (sine t / 9) * h0 - (cosine t / 9) * h1 -
        (2 * (-sine t * w 0 + cosine t * w 1) / 9) * hcs
    ext i
    fin_cases i <;> simp [firstVector]
    · linear_combination (w 0) * hcs + sine t * hu
    · linear_combination (w 1) * hcs - cosine t * hu
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact firstVector_mem t

theorem statistic_family (t : ℝ) : statistic (family t) = cosine t ^ 2 := by
  simp only [statistic, eigenspaceSeven_family]
  rw [Submodule.starProjection_unit_singleton ℝ (firstVector_norm t), norm_smul, firstVector_norm]
  simp [firstVector, firstAxis, PiLp.inner_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-! ## Two-point models (from 00000005960) -/

instance matrixMeasurableSpace : MeasurableSpace Mat2 :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → ℝ))

def fairPMF : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)

/-- The fair law on `{x, y}`. -/
def twoPointLaw {α : Type*} (x y : α) : PMF α :=
  fairPMF.map (fun i => if i = 0 then x else y)

theorem twoPointLaw_apply {α : Type*} [DecidableEq α] (x y z : α) :
    twoPointLaw x y z = (if z = x then (1 / 2 : ℝ≥0∞) else 0) +
      (if z = y then (1 / 2 : ℝ≥0∞) else 0) := by
  simp [twoPointLaw, fairPMF, PMF.map_apply, tsum_fintype, Fin.sum_univ_two,
    PMF.uniformOfFintype_apply, eq_comm]

theorem map_twoPointLaw {α β : Type*} (f : α → β) (x y : α) :
    (twoPointLaw x y).map f = twoPointLaw (f x) (f y) := by
  rw [twoPointLaw, PMF.map_comp]
  congr 1
  funext i
  simp only [Function.comp_apply]
  split_ifs <;> rfl

theorem twoPointLaw_self {α : Type*} (x : α) : twoPointLaw x x = PMF.pure x := by
  simp only [twoPointLaw, ite_self]
  exact PMF.map_const fairPMF x

theorem mem_support_twoPointLaw {α : Type*} {x y z : α} :
    z ∈ (twoPointLaw x y).support ↔ z = x ∨ z = y := by
  rw [twoPointLaw, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨i, -, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [fairPMF], rfl⟩
    · exact ⟨1, by simp [fairPMF], rfl⟩

theorem twoPointLaw_ne_pure {α : Type*} {x y : α} (hxy : x ≠ y) (z : α) :
    twoPointLaw x y ≠ PMF.pure z := by
  classical
  intro h
  have hv := congrArg (fun p : PMF α => p x) h
  have hxmass : twoPointLaw x y x = (1 / 2 : ℝ≥0∞) := by simp [twoPointLaw_apply, hxy]
  simp only [hxmass, PMF.pure_apply] at hv
  by_cases hxz : x = z <;> simp [hxz] at hv

/-- Model A: the fair law on `{F 0, F 1}`. -/
def modelA : PMF Mat2 := twoPointLaw (family 0) (family 1)

/-- Model B: the fair law on `{F (1/2), F (-1/2)}`. -/
def modelB : PMF Mat2 := twoPointLaw (family (1 / 2)) (family (-1 / 2))

/-! ## Polar decompositions -/

/-- `A = U P` with `U` orthogonal and `P` positive semidefinite. -/
def IsPolarDecomposition (A U P : Mat2) : Prop := Uᵀ * U = 1 ∧ P.PosSemidef ∧ A = U * P

theorem polar_gram {A U P : Mat2} (h : IsPolarDecomposition A U P) : P * P = Aᵀ * A := by
  obtain ⟨hU, hP, rfl⟩ := h
  have hs : Pᵀ = P := by
    have := hP.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.transpose_mul, hs, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- Uniqueness of the polar decomposition of an invertible matrix (via uniqueness of
positive square roots, `CFC.mul_self_eq_mul_self_iff`). -/
theorem polar_unique {A U P U' P' : Mat2} (hA : A.det ≠ 0) (h : IsPolarDecomposition A U P)
    (h' : IsPolarDecomposition A U' P') : U = U' ∧ P = P' := by
  have hP : P = P' := (CFC.mul_self_eq_mul_self_iff P P' h.2.1.nonneg h'.2.1.nonneg).mp
    ((polar_gram h).trans (polar_gram h').symm)
  refine ⟨?_, hP⟩
  have hdet : P.det ≠ 0 := by
    intro h0; apply hA; rw [h.2.2, det_mul, h0, mul_zero]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hdet)
  exact hPu.mul_left_injective (show U * P = U' * P by rw [← h.2.2, hP, ← h'.2.2])

def polarU0 : Mat2 := !![3 / 5, 4 / 5; 4 / 5, -3 / 5]
def polarP0 : Mat2 := !![21 / 5, 28 / 5; 28 / 5, 54 / 5]
def polarU (t : ℝ) : Mat2 := rotation t * polarU0 * (rotation t)ᵀ
def polarP (t : ℝ) : Mat2 := rotation t * polarP0 * (rotation t)ᵀ

theorem polarP0_posSemidef : polarP0.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [polarP0, conjTranspose_apply]
  · simp [polarP0, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    nlinarith [sq_nonneg (21 * x 0 + 28 * x 1), sq_nonneg (x 1)]

theorem isPolar_family (t : ℝ) : IsPolarDecomposition (family t) (polarU t) (polarP t) := by
  have hU0 : polarU0ᵀ * polarU0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [polarU0, Matrix.mul_apply, Fin.sum_univ_two]
  have hUP : polarU0 * polarP0 = seed := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [polarU0, polarP0, seed, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · simp only [polarU, transpose_mul, transpose_transpose, Matrix.mul_assoc, rotation_cancel]
    rw [← Matrix.mul_assoc polarU0ᵀ, hU0, Matrix.one_mul, rotation_mul_transpose_rotation]
  · have := polarP0_posSemidef.mul_mul_conjTranspose_same (rotation t)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  · simp only [family, polarU, polarP, Matrix.mul_assoc, rotation_cancel]
    rw [← Matrix.mul_assoc polarU0, hUP]

theorem det_family (t : ℝ) : (family t).det = -14 := by
  have h := cosine_sq_add_sine_sq t
  simp only [family, det_mul, det_transpose]
  simp [rotation, seed, det_fin_two]
  nlinarith [h]

/-! ## The conjecture -/

/-- The full claim, for models `A`, `B` and an explicit pair `X ∈ supp A`, `Y ∈ supp B`. -/
def Separation (A B : PMF Mat2) (X Y : Mat2) : Prop :=
  -- two genuine (non-Dirac) models of non-Hermitian matrices
  (∀ M ∈ A.support, ¬ M.IsHermitian) ∧ (∀ M ∈ B.support, ¬ M.IsHermitian) ∧
  (∀ N, A ≠ PMF.pure N) ∧ (∀ N, B ≠ PMF.pure N) ∧
  -- same singular spectrum (and even the same eigenvalue spectrum) ...
  A.map singularValues = B.map singularValues ∧ A.map charpoly = B.map charpoly ∧
  -- ... but different eigenvector statistics
  A.map statistic ≠ B.map statistic ∧
  -- the explicit pair: same singular values and spectrum, different polar decompositions
  X ∈ A.support ∧ Y ∈ B.support ∧
  singularValues X = singularValues Y ∧ spectrum ℝ X = spectrum ℝ Y ∧
  (∃ U P, IsPolarDecomposition X U P) ∧ (∃ U P, IsPolarDecomposition Y U P) ∧
  (∀ U P U' P', IsPolarDecomposition X U P → IsPolarDecomposition Y U' P' →
    U ≠ U' ∧ P ≠ P') ∧
  statistic X ≠ statistic Y

theorem family_zero_ne_one : family 0 ≠ family 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [family_explicit, cosine, sine] at this

theorem family_half_ne : family (1 / 2) ≠ family (-1 / 2) := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [family_explicit, cosine, sine] at this

theorem explicit_separation : Separation modelA modelB (family 0) (family (1 / 2)) := by
  have hstatA : modelA.map statistic = twoPointLaw (1 : ℝ) 0 := by
    rw [modelA, map_twoPointLaw, statistic_family, statistic_family,
      show cosine 0 ^ 2 = 1 by norm_num [cosine], show cosine 1 ^ 2 = 0 by norm_num [cosine]]
  have hstatB : modelB.map statistic = PMF.pure (9 / 25 : ℝ) := by
    rw [modelB, map_twoPointLaw, statistic_family, statistic_family,
      show cosine (1 / 2) ^ 2 = 9 / 25 by norm_num [cosine],
      show cosine (-1 / 2) ^ 2 = 9 / 25 by norm_num [cosine], twoPointLaw_self]
  refine ⟨?_, ?_, twoPointLaw_ne_pure family_zero_ne_one,
    twoPointLaw_ne_pure family_half_ne, ?_, ?_, ?_, mem_support_twoPointLaw.mpr (Or.inl rfl),
    mem_support_twoPointLaw.mpr (Or.inl rfl), by rw [singularValues_family,
      singularValues_family], by rw [spectrum_family, spectrum_family],
    ⟨_, _, isPolar_family 0⟩, ⟨_, _, isPolar_family (1 / 2)⟩, ?_, ?_⟩
  · intro M hM
    rcases mem_support_twoPointLaw.mp hM with rfl | rfl <;> exact family_not_isHermitian _
  · intro M hM
    rcases mem_support_twoPointLaw.mp hM with rfl | rfl <;> exact family_not_isHermitian _
  · simp only [modelA, modelB, map_twoPointLaw, singularValues_family]
  · simp only [modelA, modelB, map_twoPointLaw, charpoly_family]
  · rw [hstatA, hstatB]
    intro h
    have := congrArg (fun p : PMF ℝ => p 0) h
    simp [twoPointLaw_apply, PMF.pure_apply] at this
    norm_num at this
  · intro U P U' P' hX hY
    obtain ⟨rfl, rfl⟩ := polar_unique (by rw [det_family]; norm_num) hX (isPolar_family 0)
    obtain ⟨rfl, rfl⟩ :=
      polar_unique (by rw [det_family]; norm_num) hY (isPolar_family (1 / 2))
    constructor
    · intro h
      have := congrFun (congrFun h 0) 0
      norm_num [polarU, polarU0, rotation, cosine, sine, Matrix.mul_apply,
        Fin.sum_univ_two] at this
    · intro h
      have := congrFun (congrFun h 0) 0
      norm_num [polarP, polarP0, rotation, cosine, sine, Matrix.mul_apply,
        Fin.sum_univ_two] at this
  · rw [statistic_family, statistic_family]; norm_num [cosine]

/-- **Conjecture 00000005980.** -/
theorem conjecture_5980 : ∃ (A B : PMF Mat2) (X Y : Mat2), Separation A B X Y :=
  ⟨_, _, _, _, explicit_separation⟩

end C5980
