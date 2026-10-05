import Mathlib

/-
Conjecture 00000005600 (The Last Math Competition): same determinant, different
echelon form, separated by an explicit noncommutative pair of unimodular transformations.

Integer matrices: `M = [[1,-4],[0,4]]`, `N = [[2,0],[-2,2]]` (det 4 each), and
`U = [[1,1],[0,1]]`, `V = [[1,0],[1,1]] ∈ GL₂(ℤ)` with `UV ≠ VU`.  `U` reduces `M` to the
Hermite form `diag(1,4)`, `V` reduces `N` to `diag(2,2)`; the cokernels are
`ℤ/4` and `(ℤ/2)²`.  Second reading: `X UV` and `X VU` (`X = diag(1,2)`) have equal
determinants but distinct Hermite forms.

Adapted from the accepted solution of the near-duplicate 00000006330
(solutions/00000006330/gaochengzhecpu_submission_20261003215646, GPL-3.0): the pair
diag(1,4), diag(2,2) and the parity obstruction to two-sided equivalence come from there.
-/

open Matrix

namespace Conjecture5600

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

/-- Unimodular row equivalence: `H = W * M` with `W` in Mathlib's `GL (Fin 2) ℤ`
(integer matrices with integer inverse, i.e. determinant `±1`). -/
def RowEquiv (M H : Mat) : Prop := ∃ W : GL (Fin 2) ℤ, (W : Mat) * M = H

/-- Row-style Hermite normal form of a nonsingular square integer matrix: upper
triangular, positive pivots on the diagonal, and every entry above a pivot lies in
`[0, pivot)`. -/
def IsHermiteNormalForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, j < i → H i j = 0) ∧ (∀ i, 0 < H i i) ∧
  (∀ i j, i < j → 0 ≤ H i j ∧ H i j < H j j)

/-- The row module (row lattice) of `X`: all integer combinations `w ᵥ* X` of its rows. -/
def rowModule (X : Mat) : Submodule ℤ (Fin 2 → ℤ) := LinearMap.range X.vecMulLinear

theorem rowModule_eq_span (X : Mat) : rowModule X = Submodule.span ℤ (Set.range X.row) :=
  _root_.range_vecMulLinear X

/-- The cokernel `ℤ² / (row module of X)`, the isomorphism type of an echelon form. -/
abbrev coker (X : Mat) := (Fin 2 → ℤ) ⧸ rowModule X

theorem rowModule_unit_mul (W : GL (Fin 2) ℤ) (X : Mat) :
    rowModule ((W : Mat) * X) = rowModule X := by
  ext v
  simp only [rowModule, LinearMap.mem_range, Matrix.vecMulLinear_apply]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨w ᵥ* (W : Mat), by rw [Matrix.vecMul_vecMul]⟩
  · rintro ⟨w, rfl⟩
    refine ⟨w ᵥ* ((W⁻¹ : GL (Fin 2) ℤ) : Mat), ?_⟩
    rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]

theorem rowModule_of_rowEquiv {X H : Mat} (h : RowEquiv X H) : rowModule H = rowModule X := by
  obtain ⟨W, rfl⟩ := h; exact rowModule_unit_mul W X

def gl2 (a b c d : ℤ) (h : a * d - b * c = 1) : GL (Fin 2) ℤ :=
  ⟨!![a, b; c, d], !![d, -b; -c, a], by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith,
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith⟩

/-- The two standard elementary (transvection) generators of `SL₂(ℤ)`. -/
def U : GL (Fin 2) ℤ := gl2 1 1 0 1 (by norm_num)
def V : GL (Fin 2) ℤ := gl2 1 0 1 1 (by norm_num)

theorem U_val : (U : Mat) = !![1, 1; 0, 1] := rfl
theorem V_val : (V : Mat) = !![1, 0; 1, 1] := rfl

theorem det_U : (U : Mat).det = 1 := by simp [U_val, Matrix.det_fin_two]
theorem det_V : (V : Mat).det = 1 := by simp [V_val, Matrix.det_fin_two]

theorem U_V_noncomm : U * V ≠ V * U := by
  intro h
  have := congrArg (fun g : GL (Fin 2) ℤ => (g : Mat) 0 0) h
  simp [U_val, V_val, Matrix.mul_apply, Fin.sum_univ_two] at this

/-! Reading A: two matrices brought to their echelon forms by `U` and `V`. -/

def M : Mat := !![1, -4; 0, 4]
def N : Mat := !![2, 0; -2, 2]

theorem U_mul_M : (U : Mat) * M = !![1, 0; 0, 4] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U_val, M, Matrix.mul_apply, Fin.sum_univ_two]

theorem V_mul_N : (V : Mat) * N = !![2, 0; 0, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [V_val, N, Matrix.mul_apply, Fin.sum_univ_two]

theorem hnf_of_diag (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    IsHermiteNormalForm (!![a, 0; 0, b] : Mat) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simp [ha, hb]
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all

theorem det_M : M.det = 4 := by simp [M, Matrix.det_fin_two]
theorem det_N : N.det = 4 := by simp [N, Matrix.det_fin_two]

theorem mem_rowModule_M (v : Fin 2 → ℤ) :
    v ∈ rowModule M ↔ ∃ w : Fin 2 → ℤ, w 0 = v 0 ∧ -4 * w 0 + 4 * w 1 = v 1 := by
  simp only [rowModule, LinearMap.mem_range, Matrix.vecMulLinear_apply, funext_iff, Fin.forall_fin_two]
  simp [M, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  constructor <;> rintro ⟨w, h0, h1⟩ <;> exact ⟨w, by linarith, by linarith⟩

theorem mem_rowModule_N (v : Fin 2 → ℤ) :
    v ∈ rowModule N ↔ ∃ w : Fin 2 → ℤ, 2 * w 0 - 2 * w 1 = v 0 ∧ 2 * w 1 = v 1 := by
  simp only [rowModule, LinearMap.mem_range, Matrix.vecMulLinear_apply, funext_iff, Fin.forall_fin_two]
  simp [N, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  constructor <;> rintro ⟨w, h0, h1⟩ <;> exact ⟨w, by linarith, by linarith⟩

/-- Every element of the cokernel of any matrix row-equivalent to `N` is 2-torsion. -/
theorem coker_N_two_torsion {H : Mat} (h : RowEquiv N H) (y : coker H) : y + y = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero, rowModule_of_rowEquiv h,
    mem_rowModule_N]
  exact ⟨fun k => if k = 0 then v 0 + v 1 else v 1, by simp; ring, by simp; ring⟩

/-- The cokernel of any matrix row-equivalent to `M` has an element `x` with `x + x ≠ 0`. -/
theorem coker_M_not_two_torsion {H : Mat} (h : RowEquiv M H) :
    ∃ x : coker H, x + x ≠ 0 := by
  refine ⟨Submodule.Quotient.mk ![0, 1], ?_⟩
  rw [← Submodule.Quotient.mk_add, Ne, Submodule.Quotient.mk_eq_zero, rowModule_of_rowEquiv h,
    mem_rowModule_M]
  rintro ⟨w, h0, h1⟩
  simp at h0 h1
  omega

theorem coker_not_iso {H₁ H₂ : Mat} (h₁ : RowEquiv M H₁) (h₂ : RowEquiv N H₂) :
    IsEmpty (coker H₁ ≃+ coker H₂) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, hx⟩ := coker_M_not_two_torsion h₁
  apply hx
  apply e.injective
  rw [map_add, map_zero]
  exact coker_N_two_torsion h₂ (e x)

/-- All entries of `P * N * Q` are even, while `M 0 0 = 1`: no two-sided equivalence. -/
theorem not_two_sided (P Q : GL (Fin 2) ℤ) : (P : Mat) * N * Q ≠ M := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have key : ((P : Mat) * N * Q) 0 0 = 2 * ((P 0 0 - P 0 1) * Q 0 0 + P 0 1 * Q 1 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hM : M 0 0 = 1 := by simp [M]
  rw [key, hM] at h00
  generalize (P 0 0 - P 0 1) * Q 0 0 + P 0 1 * Q 1 0 = t at h00
  omega

/-! Reading B: the same base matrix, transformed by `U, V` in the two orders. -/

def X : Mat := !![1, 0; 0, 2]

theorem XUV : X * (U : Mat) * (V : Mat) = !![2, 1; 2, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, U_val, V_val, Matrix.mul_apply, Fin.sum_univ_two]
theorem XVU : X * (V : Mat) * (U : Mat) = !![1, 1; 2, 4] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, U_val, V_val, Matrix.mul_apply, Fin.sum_univ_two]

theorem echelon_XUV : RowEquiv (X * (U : Mat) * (V : Mat)) !![2, 0; 0, 1] ∧
    IsHermiteNormalForm (!![2, 0; 0, 1] : Mat) := by
  refine ⟨⟨gl2 2 (-1) (-1) 1 (by norm_num), ?_⟩, hnf_of_diag 2 1 (by norm_num) (by norm_num)⟩
  rw [XUV]; ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, Matrix.mul_apply, Fin.sum_univ_two]

theorem echelon_XVU : RowEquiv (X * (V : Mat) * (U : Mat)) !![1, 1; 0, 2] ∧
    IsHermiteNormalForm (!![1, 1; 0, 2] : Mat) := by
  refine ⟨⟨gl2 1 0 (-2) 1 (by norm_num), ?_⟩, ?_⟩
  · rw [XVU]; ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨?_, ?_, ?_⟩
    · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i <;> simp
    · intro i j h; fin_cases i <;> fin_cases j <;> simp_all

theorem readingB_separated {H₁ H₂ : Mat} (h₁ : RowEquiv (X * (U : Mat) * (V : Mat)) H₁)
    (h₂ : RowEquiv (X * (V : Mat) * (U : Mat)) H₂) : H₁ ≠ H₂ := by
  rintro rfl
  have h := (rowModule_of_rowEquiv h₁).symm.trans (rowModule_of_rowEquiv h₂)
  have hmem : ![1, 1] ∈ rowModule (X * (V : Mat) * (U : Mat)) :=
    ⟨![1, 0], by rw [XVU]; ext k; fin_cases k <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]⟩
  rw [← h] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [XUV] at hw
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
  omega

/-- **Conjecture 00000005600.** -/
theorem conjecture_5600 :
    ∃ (A B : Mat) (U V : GL (Fin 2) ℤ),
      -- an explicit noncommutative pair of unimodular transformations
      (U : Mat).det = 1 ∧ (V : Mat).det = 1 ∧ U * V ≠ V * U ∧
      -- Reading A: same determinant, `U`, `V` reduce `A`, `B` to distinct Hermite forms
      A.det = B.det ∧
      IsHermiteNormalForm ((U : Mat) * A) ∧ IsHermiteNormalForm ((V : Mat) * B) ∧
      (U : Mat) * A ≠ (V : Mat) * B ∧
      (∀ H₁ H₂, RowEquiv A H₁ → RowEquiv B H₂ → H₁ ≠ H₂) ∧
      (∀ H₁ H₂, RowEquiv A H₁ → RowEquiv B H₂ → IsEmpty (coker H₁ ≃+ coker H₂)) ∧
      (∀ P Q : GL (Fin 2) ℤ, (P : Mat) * B * Q ≠ A) ∧
      -- Reading B: a base matrix moved by `U V` and by `V U`
      ∃ Y : Mat, (Y * (U : Mat) * (V : Mat)).det = (Y * (V : Mat) * (U : Mat)).det ∧
        (∀ H₁ H₂, RowEquiv (Y * (U : Mat) * (V : Mat)) H₁ → RowEquiv (Y * (V : Mat) * (U : Mat)) H₂ → H₁ ≠ H₂) ∧
        (∃ H₁ H₂, RowEquiv (Y * (U : Mat) * (V : Mat)) H₁ ∧ IsHermiteNormalForm H₁ ∧
          RowEquiv (Y * (V : Mat) * (U : Mat)) H₂ ∧ IsHermiteNormalForm H₂) := by
  refine ⟨M, N, U, V, det_U, det_V, U_V_noncomm, det_M.trans det_N.symm, ?_, ?_, ?_,
    fun H₁ H₂ h₁ h₂ heq => ?_, fun H₁ H₂ h₁ h₂ => coker_not_iso h₁ h₂, not_two_sided,
    X, ?_, fun H₁ H₂ h₁ h₂ => readingB_separated h₁ h₂,
    ⟨_, _, echelon_XUV.1, echelon_XUV.2, echelon_XVU.1, echelon_XVU.2⟩⟩
  · rw [U_mul_M]; exact hnf_of_diag 1 4 (by norm_num) (by norm_num)
  · rw [V_mul_N]; exact hnf_of_diag 2 2 (by norm_num) (by norm_num)
  · rw [U_mul_M, V_mul_N]; intro h
    have := congrFun (congrFun h 0) 0; simp at this
  · subst heq
    exact (coker_not_iso h₁ h₂).false (AddEquiv.refl _)
  · rw [XUV, XVU]; simp [Matrix.det_fin_two]

end Conjecture5600
