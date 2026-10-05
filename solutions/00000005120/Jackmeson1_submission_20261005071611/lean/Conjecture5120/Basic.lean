import Mathlib

/-!
Conjecture 00000005120 (The Last Math Competition).

Definition: the spectrum and the function condition number are two layers of sensitivity.
Conjecture: there exist two matrices with the same spectrum but exponentially different
matrix-function condition numbers, and the separation is realized by an explicit pair of
Jordan structures.

Witnesses, for every `n ≥ 2` (real `n × n` matrices):
* `A n = (1/2) • 1`, the Jordan matrix with `n` Jordan blocks of size `1` for the eigenvalue `1/2`;
* `B n = J_n(1/2) = (1/2) • 1 + N`, a single Jordan block (`N` = ones on the superdiagonal).

Matrix function: `f(x) = 1/x`, i.e. `f(X) = X⁻¹` (Mathlib `Ring.inverse`).
Condition number (Higham, *Functions of Matrices*, Def. 3.1 and Thm 3.1): the absolute
condition number `cond(f, X) = ‖L_f(X)‖`, the operator norm of the Fréchet derivative
`L_f(X) = fderiv ℝ f X`, for the matrix norm `‖M‖∞ = max_i Σ_j |M i j|`
(Mathlib `Matrix.linftyOpNormedRing`, the operator norm induced by the sup norm on `ℝⁿ`).

Results: the same characteristic polynomial `(X - 1/2)^n` and the same spectrum `{1/2}`; the two
are not similar (different Jordan structures); `cond(f, A n) = 4` but `cond(f, B n) ≥ 4^n`.
-/

namespace Conjecture5120

open Matrix Polynomial

variable (n : ℕ)

/-! ### Matrices and the two Jordan structures -/

/-- The nilpotent shift: ones on the superdiagonal. -/
def shift : Matrix (Fin n) (Fin n) ℝ := fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- The Jordan block `J_n(λ) = λ I + N`. -/
noncomputable def jordanBlock (lam : ℝ) : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix _ _ ℝ) + shift n

/-- The Jordan matrix `λ I` (`n` Jordan blocks of size `1`). -/
noncomputable def scalarJordan (lam : ℝ) : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix _ _ ℝ)

/-- First witness: the diagonal Jordan structure for the eigenvalue `1/2`. -/
noncomputable def A : Matrix (Fin n) (Fin n) ℝ := scalarJordan n (1 / 2)

/-- Second witness: one Jordan block of size `n` for the eigenvalue `1/2`. -/
noncomputable def B : Matrix (Fin n) (Fin n) ℝ := jordanBlock n (1 / 2)

/-! ### Same spectrum -/

theorem A_upper : (A n).IsUpperTriangular := by
  intro i j hij
  have hij' : j < i := hij
  simp [A, scalarJordan, one_apply, hij'.ne']

theorem B_upper : (B n).IsUpperTriangular := by
  intro i j hij
  have hij' : j < i := hij
  have h1 : (j : ℕ) ≠ i + 1 := by have := Fin.lt_def.mp hij'; omega
  simp [B, jordanBlock, shift, one_apply, hij'.ne', h1]

theorem charpoly_A : (A n).charpoly = (X - C (1 / 2 : ℝ)) ^ n := by
  rw [charpoly_of_isUpperTriangular _ (A_upper n)]
  simp [A, scalarJordan]

theorem charpoly_B : (B n).charpoly = (X - C (1 / 2 : ℝ)) ^ n := by
  rw [charpoly_of_isUpperTriangular _ (B_upper n)]
  simp [B, jordanBlock, shift]

theorem spectrum_of_charpoly {M : Matrix (Fin n) (Fin n) ℝ} (hn : n ≠ 0)
    (h : M.charpoly = (X - C (1 / 2 : ℝ)) ^ n) : spectrum ℝ M = {1 / 2} := by
  ext r
  rw [mem_spectrum_iff_isRoot_charpoly, h, Set.mem_singleton_iff, IsRoot.def, eval_pow,
    eval_sub, eval_X, eval_C, pow_eq_zero_iff hn, sub_eq_zero]

/-! ### Different Jordan structures -/

theorem shift_ne_zero (hn : 2 ≤ n) : shift n ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  simp [shift] at this

/-- `B n` is not similar to `A n`: a scalar matrix is similar only to itself. -/
theorem not_similar (hn : 2 ≤ n) :
    ¬ ∃ P : (Matrix (Fin n) (Fin n) ℝ)ˣ,
      B n = (P : Matrix (Fin n) (Fin n) ℝ) * A n * (↑(P⁻¹) : Matrix (Fin n) (Fin n) ℝ) := by
  rintro ⟨P, hP⟩
  have hA : (P : Matrix (Fin n) (Fin n) ℝ) * A n * (↑(P⁻¹) : Matrix (Fin n) (Fin n) ℝ) = A n := by
    rw [A, scalarJordan, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]
  rw [hA, A, B, jordanBlock, scalarJordan, add_eq_left] at hP
  exact shift_ne_zero n hn hP

/-! ### The inverse of the Jordan block -/

/-- Entries of `J_n(1/2)⁻¹`: `(-1)^(j-i) 2^(j-i+1)` on and above the diagonal. -/
noncomputable def c (i j : ℕ) : ℝ := if i ≤ j then (-1) ^ (j - i) * 2 ^ (j - i + 1) else 0

noncomputable def Binv : Matrix (Fin n) (Fin n) ℝ := fun i j => c i j

theorem shift_mul_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (shift n * M) i j = if h : (i : ℕ) + 1 < n then M ⟨i + 1, h⟩ j else 0 := by
  simp only [mul_apply, shift, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i + 1, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (Fin.ext hb')
    · simp
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro hk
    exact h (hk ▸ k.isLt)

theorem key (a b : ℕ) (hb : b < n) :
    1 / 2 * c a b + (if a + 1 < n then c (a + 1) b else 0) = if a = b then 1 else 0 := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : a + 1 < n := by omega
    have h2 : a ≠ a + e + 1 := by omega
    rw [if_pos h1, if_neg h2]
    simp only [c, if_pos (show a ≤ a + e + 1 by omega), if_pos (show a + 1 ≤ a + e + 1 by omega),
      show a + e + 1 - a = e + 1 by omega, show a + e + 1 - (a + 1) = e by omega]
    ring
  · subst heq
    simp [c]
  · have h1 : ¬ a ≤ b := by omega
    have h2 : ¬ a + 1 ≤ b := by omega
    simp [c, h1, h2, hgt.ne']

theorem B_mul_Binv : B n * Binv n = 1 := by
  ext i j
  rw [B, jordanBlock, add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.add_apply, Matrix.smul_apply,
    shift_mul_apply, one_apply]
  have := key n i j j.isLt
  simp only [Binv, smul_eq_mul] at this ⊢
  split_ifs at this ⊢ <;> simp_all [Fin.ext_iff]

theorem Binv_mul_B : Binv n * B n = 1 := mul_eq_one_comm.mp (B_mul_Binv n)

/-! ### The normed algebra of matrices and the condition number -/

/-- Real `n × n` matrices with the `∞`-operator norm `‖M‖ = max_i Σ_j |M i j|`. -/
def Mat : Type := Matrix (Fin n) (Fin n) ℝ

noncomputable instance : NormedRing (Mat n) := Matrix.linftyOpNormedRing
noncomputable instance : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
instance : FiniteDimensional ℝ (Mat n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℝ))
instance : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)

/-- Absolute condition number of a matrix function `f` at `X`: the operator norm of its
Fréchet derivative `L_f(X)`. -/
noncomputable def cond (f : Mat n → Mat n) (X : Mat n) : ℝ := ‖fderiv ℝ f X‖

/-- The matrix function `f(X) = X⁻¹` of `f(x) = 1/x`. -/
noncomputable def inv : Mat n → Mat n := Ring.inverse

theorem norm_def (M : Mat n) : ‖M‖ = ((Finset.univ : Finset (Fin n)).sup
    fun i => ∑ j, ‖(show Matrix (Fin n) (Fin n) ℝ from M) i j‖₊ : NNReal) := by
  let _ := (Matrix.linftyOpNormedRing : NormedRing (Matrix (Fin n) (Fin n) ℝ))
  exact Matrix.linfty_opNorm_def (show Matrix (Fin n) (Fin n) ℝ from M)

theorem entry_le_norm (M : Mat n) (i j : Fin n) :
    ‖(show Matrix (Fin n) (Fin n) ℝ from M) i j‖ ≤ ‖M‖ := by
  rw [norm_def]
  set M' : Matrix (Fin n) (Fin n) ℝ := M
  have h1 : ‖M' i j‖₊ ≤ ∑ k, ‖M' i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖M' i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : ∑ k, ‖M' i k‖₊ ≤ Finset.univ.sup fun i => ∑ k, ‖M' i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖M' i k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

theorem norm_single_le (p q : Fin n) :
    ‖(show Mat n from (Matrix.single p q (1 : ℝ) : Matrix (Fin n) (Fin n) ℝ))‖ ≤ 1 := by
  rw [norm_def]
  norm_cast
  apply Finset.sup_le
  intro i _
  by_cases hi : p = i
  · subst hi
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [hi]

/-- `A n` as a unit of `Mat n`, with inverse `2 • 1`. -/
noncomputable def Aunit : (Mat n)ˣ where
  val := A n
  inv := (show Mat n from (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
  val_inv := by
    change A n * ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1
    rw [A, scalarJordan, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num
  inv_val := by
    change ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) * A n = 1
    rw [A, scalarJordan, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num

/-- `B n` as a unit of `Mat n`, with inverse `Binv n`. -/
noncomputable def Bunit : (Mat n)ˣ := ⟨B n, Binv n, B_mul_Binv n, Binv_mul_B n⟩

theorem cond_A (hn : n ≠ 0) : cond n (inv n) (A n) = 4 := by
  have : NeZero n := ⟨hn⟩
  have : Nontrivial (Mat n) := inferInstanceAs (Nontrivial (Matrix (Fin n) (Fin n) ℝ))
  have h := fderiv_inverse (𝕜 := ℝ) (Aunit n)
  set L := ContinuousLinearMap.mulLeftRight ℝ (Mat n) ↑(Aunit n)⁻¹ ↑(Aunit n)⁻¹ with hLdef
  have hL : ∀ E, L E = (4 : ℝ) • E := by
    intro E
    rw [hLdef, ContinuousLinearMap.mulLeftRight_apply]
    change ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) * (show Matrix (Fin n) (Fin n) ℝ from E) *
      ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = (4 : ℝ) • (show Matrix (Fin n) (Fin n) ℝ from E)
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  unfold cond inv
  change ‖fderiv ℝ Ring.inverse ((Aunit n : Mat n))‖ = 4
  rw [h, norm_neg]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro E
    rw [hL, norm_smul]
    norm_num
  · obtain ⟨E, hE⟩ := exists_ne (0 : Mat n)
    have h1 := L.le_opNorm E
    rw [hL, norm_smul] at h1
    have h2 : 0 < ‖E‖ := norm_pos_iff.mpr hE
    norm_num at h1
    nlinarith

/-- The `(0, n-1)` entry of `J⁻¹ E J⁻¹` for `E = e_{n-1} e_0ᵀ` is `(J⁻¹)_{0,n-1}² = 4^n`. -/
theorem entry_calc (hn : n ≠ 0) :
    (Binv n * Matrix.single (⟨n - 1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n) (1 : ℝ) * Binv n)
      ⟨0, by omega⟩ ⟨n - 1, by omega⟩ = (4 : ℝ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : ((2 : ℝ) ^ (m + 1)) ^ 2 = 4 ^ (m + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (m + 1))]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨m, by omega⟩ : Fin (m + 1))]
    · simp only [Binv, c, Matrix.single_apply, and_self, if_true, mul_one, Nat.zero_le,
        Nat.sub_zero]
      calc (-1) ^ m * 2 ^ (m + 1) * ((-1) ^ m * 2 ^ (m + 1))
          = ((-1 : ℝ) ^ m) ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 := by ring
        _ = (4 : ℝ) ^ (m + 1) := by rw [h1, h2, one_mul]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro k _
    simp only [Matrix.single_apply]
    split_ifs with h0
    · exact absurd (Fin.ext (by rw [← h0.2])) hb
    · simp
  · simp

theorem cond_B (hn : n ≠ 0) : (4 : ℝ) ^ n ≤ cond n (inv n) (B n) := by
  have h := fderiv_inverse (𝕜 := ℝ) (Bunit n)
  let z : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n - 1, by omega⟩
  let E : Mat n := (show Mat n from (Matrix.single l z (1 : ℝ) : Matrix (Fin n) (Fin n) ℝ))
  have hE : ‖E‖ ≤ 1 := norm_single_le n l z
  have hentry : (show Matrix (Fin n) (Fin n) ℝ from
      fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n) E) z l = -(4 : ℝ) ^ n := by
    rw [h]
    change -((Binv n * Matrix.single l z (1 : ℝ) * Binv n : Matrix (Fin n) (Fin n) ℝ) z l) = _
    rw [entry_calc n hn]
  unfold cond inv
  change (4 : ℝ) ^ n ≤ ‖fderiv ℝ Ring.inverse ((Bunit n : Mat n))‖
  calc (4 : ℝ) ^ n = ‖(show Matrix (Fin n) (Fin n) ℝ from
        fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n) E) z l‖ := by
          rw [hentry, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ ‖fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n) E‖ := entry_le_norm n _ z l
    _ ≤ ‖fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n)‖ * ‖E‖ :=
          (fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n)).le_opNorm E
    _ ≤ ‖fderiv ℝ (Ring.inverse : Mat n → Mat n) (Bunit n : Mat n)‖ :=
          mul_le_of_le_one_right (norm_nonneg _) hE

/-! ### Relative condition numbers -/

/-- Relative condition number `cond_rel(f, X) = cond(f, X) ‖X‖ / ‖f X‖` (Higham, eq. (3.2)). -/
noncomputable def condRel (f : Mat n → Mat n) (X : Mat n) : ℝ := cond n f X * ‖X‖ / ‖f X‖

theorem norm_le_of_rows (M : Mat n) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, ∑ j, |(show Matrix (Fin n) (Fin n) ℝ from M) i j| ≤ K) : ‖M‖ ≤ K := by
  rw [norm_def]
  set M' : Matrix (Fin n) (Fin n) ℝ := M
  have : (Finset.univ.sup fun i => ∑ j, ‖M' i j‖₊) ≤ ⟨K, hK⟩ := Finset.sup_le fun i _ => by
    apply NNReal.coe_le_coe.1
    push_cast
    show ∑ j, ‖M' i j‖ ≤ K
    simpa [Real.norm_eq_abs] using h i
  exact_mod_cast this

theorem geom_sum_two (m : ℕ) : ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) = 2 ^ (m + 1) - 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem abs_c_le (i j : ℕ) : |c i j| ≤ 2 ^ (j + 1) := by
  unfold c
  split_ifs with h
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_two]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · simp

theorem norm_Binv_le : ‖(show Mat n from Binv n)‖ ≤ 2 ^ (n + 1) := by
  apply norm_le_of_rows n _ _ (by positivity)
  intro i
  calc ∑ j, |Binv n i j| ≤ ∑ j : Fin n, (2 : ℝ) ^ ((j : ℕ) + 1) :=
        Finset.sum_le_sum fun j _ => abs_c_le i j
    _ = ∑ j ∈ Finset.range n, (2 : ℝ) ^ (j + 1) :=
        Fin.sum_univ_eq_sum_range (fun j => (2 : ℝ) ^ (j + 1)) n
    _ ≤ 2 ^ (n + 1) := by rw [geom_sum_two]; linarith

theorem norm_Binv_pos (hn : n ≠ 0) : 0 < ‖(show Mat n from Binv n)‖ := by
  have h := entry_le_norm n (show Mat n from Binv n) ⟨0, by omega⟩ ⟨0, by omega⟩
  have : (show Matrix (Fin n) (Fin n) ℝ from Binv n) ⟨0, by omega⟩ ⟨0, by omega⟩ = 2 := by
    simp [Binv, c]
  rw [this] at h
  norm_num at h
  linarith

theorem norm_B_ge (hn : n ≠ 0) : 1 / 2 ≤ ‖(show Mat n from B n)‖ := by
  have h := entry_le_norm n (show Mat n from B n) ⟨0, by omega⟩ ⟨0, by omega⟩
  have : (show Matrix (Fin n) (Fin n) ℝ from B n) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 / 2 := by
    simp [B, jordanBlock, shift]
  rw [this] at h
  norm_num at h ⊢
  exact h

theorem norm_scalar (hn : n ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    ‖(show Mat n from a • (1 : Matrix (Fin n) (Fin n) ℝ))‖ = a := by
  apply le_antisymm
  · apply norm_le_of_rows n _ _ ha
    intro i
    rw [Finset.sum_eq_single i]
    · simp [abs_of_nonneg ha]
    · intro b _ hb; simp [one_apply, Ne.symm hb]
    · simp
  · have h := entry_le_norm n (show Mat n from a • (1 : Matrix (Fin n) (Fin n) ℝ))
      ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa [abs_of_nonneg ha] using h

theorem condRel_A (hn : n ≠ 0) : condRel n (inv n) (A n) = 1 := by
  have hinv : inv n (A n) = ((Aunit n)⁻¹ : (Mat n)ˣ) := Ring.inverse_unit (Aunit n)
  unfold condRel
  rw [cond_A n hn, hinv]
  change 4 * ‖(show Mat n from (1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))‖ /
    ‖(show Mat n from (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))‖ = 1
  rw [norm_scalar n hn _ (by norm_num), norm_scalar n hn _ (by norm_num)]
  norm_num

theorem condRel_B (hn : n ≠ 0) : 2 ^ n / 4 ≤ condRel n (inv n) (B n) := by
  have hinv : inv n (B n) = ((Bunit n)⁻¹ : (Mat n)ˣ) := Ring.inverse_unit (Bunit n)
  unfold condRel
  rw [hinv]
  change 2 ^ n / 4 ≤ cond n (inv n) (B n) * ‖(show Mat n from B n)‖ /
    ‖(show Mat n from Binv n)‖
  have h1 := cond_B n hn
  have h2 := norm_B_ge n hn
  have h3 := norm_Binv_le n
  have h4 := norm_Binv_pos n hn
  rw [le_div_iff₀ h4]
  have h5 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have h6 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have h7 : (0 : ℝ) < 2 ^ n := by positivity
  calc 2 ^ n / 4 * ‖(show Mat n from Binv n)‖ ≤ 2 ^ n / 4 * 2 ^ (n + 1) := by gcongr
    _ = 4 ^ n * (1 / 2) := by rw [h5, h6]; ring
    _ ≤ cond n (inv n) (B n) * ‖(show Mat n from B n)‖ := by
        gcongr
        exact le_trans (by positivity) h1

/-! ### Main theorem -/

/-- **Conjecture 00000005120.** For every `n ≥ 2` the two Jordan structures for the eigenvalue
`1/2` — `A n = (1/2) I` (`n` blocks of size `1`) and `B n = J_n(1/2)` (one block of size `n`) —
have the same characteristic polynomial and the same spectrum `{1/2}` and are not similar,
while the condition numbers of the matrix function `X ↦ X⁻¹` (`∞`-norm) differ exponentially:
absolute `4` versus at least `4^n`, relative `1` versus at least `2^n / 4`. -/
theorem conjecture_5120 (n : ℕ) (hn : 2 ≤ n) :
    A n = scalarJordan n (1 / 2) ∧ B n = jordanBlock n (1 / 2) ∧
    (A n).charpoly = (B n).charpoly ∧
    spectrum ℝ (A n) = {1 / 2} ∧ spectrum ℝ (B n) = {1 / 2} ∧
    (¬ ∃ P : (Matrix (Fin n) (Fin n) ℝ)ˣ,
      B n = (P : Matrix (Fin n) (Fin n) ℝ) * A n * (↑(P⁻¹) : Matrix (Fin n) (Fin n) ℝ)) ∧
    cond n (inv n) (A n) = 4 ∧ (4 : ℝ) ^ n ≤ cond n (inv n) (B n) ∧
    (4 : ℝ) ^ (n - 1) * cond n (inv n) (A n) ≤ cond n (inv n) (B n) ∧
    condRel n (inv n) (A n) = 1 ∧ (2 : ℝ) ^ n / 4 ≤ condRel n (inv n) (B n) := by
  have hn0 : n ≠ 0 := by omega
  refine ⟨rfl, rfl, by rw [charpoly_A, charpoly_B], spectrum_of_charpoly n hn0 (charpoly_A n),
    spectrum_of_charpoly n hn0 (charpoly_B n), not_similar n hn, cond_A n hn0, cond_B n hn0,
    ?_, condRel_A n hn0, condRel_B n hn0⟩
  rw [cond_A n hn0]
  have h : (4 : ℝ) ^ (n - 1) * 4 = 4 ^ n := by
    rw [← pow_succ]; congr 1; omega
  rw [h]
  exact cond_B n hn0

end Conjecture5120
