import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Conjecture236

open scoped BigOperators ComplexOrder
open Matrix

/-- A dimension-independent determinant estimate for nonnegative eigenvalues. -/
theorem product_gap {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = n)
    (hvar : (1 : ℝ) / 2 ≤ ∑ i, (x i - 1) ^ 2) :
    ∏ i, x i ≤ Real.exp (-(1 / 18 : ℝ)) := by
  let S : ℝ := ∑ i, (Real.sqrt (x i) - 1) ^ 2
  have hS : (1 : ℝ) / 18 ≤ S := by
    by_contra h
    have hs : S < 1 / 18 := lt_of_not_ge h
    have hpoint (i : Fin n) : (x i - 1) ^ 2 ≤ 9 * (Real.sqrt (x i) - 1) ^ 2 := by
      have hi : (Real.sqrt (x i) - 1) ^ 2 ≤ S :=
        Finset.single_le_sum (fun j _ => sq_nonneg (Real.sqrt (x j) - 1)) (Finset.mem_univ i)
      have hsqrt := Real.sq_sqrt (hx i)
      have hsqrt0 := Real.sqrt_nonneg (x i)
      have hsqrt2 : Real.sqrt (x i) ≤ 2 := by nlinarith
      have hfactor : (Real.sqrt (x i) + 1) ^ 2 ≤ 9 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hfactor (sq_nonneg (Real.sqrt (x i) - 1))
      nlinarith [sq_nonneg (x i - 1)]
    have hv : (∑ i, (x i - 1) ^ 2) ≤ 9 * S := by
      simpa only [S, Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hpoint i)
    linarith
  have hexp (i : Fin n) : x i ≤ Real.exp (2 * (Real.sqrt (x i) - 1)) := by
    have h := Real.add_one_le_exp (Real.sqrt (x i) - 1)
    have hsq : (Real.sqrt (x i)) ^ 2 ≤ (Real.exp (Real.sqrt (x i) - 1)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith) 2
    simpa only [Real.sq_sqrt (hx i), ← Real.exp_nat_mul, Nat.cast_ofNat] using hsq
  have hsum' : (∑ i, 2 * (Real.sqrt (x i) - 1)) = -S := by
    have hid (i : Fin n) : 2 * (Real.sqrt (x i) - 1) =
        x i - 1 - (Real.sqrt (x i) - 1) ^ 2 := by
      nlinarith [Real.sq_sqrt (hx i)]
    simp_rw [hid]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hsum, sub_self, zero_sub, S]
  calc
    ∏ i, x i ≤ ∏ i, Real.exp (2 * (Real.sqrt (x i) - 1)) :=
      Finset.prod_le_prod (fun i _ => hx i) (fun i _ => hexp i)
    _ = Real.exp (-S) := by rw [← Real.exp_sum, hsum']
    _ ≤ Real.exp (-(1 / 18 : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hS)

/-- Trace and the sum of squared entries expressed through real eigenvalues. -/
theorem spectral_moments {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.IsHermitian) :
    (∑ i, hG.eigenvalues i) = G.trace ∧
    (∑ i, (hG.eigenvalues i) ^ 2) = (G * G).trace := by
  let U : Matrix (Fin n) (Fin n) ℝ := hG.eigenvectorUnitary
  let L : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hG.eigenvalues
  have hrepr : G = U * L * star U := by simpa [U, L] using hG.spectral_theorem
  have hU : star U * U = 1 := unitary.coe_star_mul_self hG.eigenvectorUnitary
  constructor
  · conv_rhs => rw [hrepr, Matrix.trace_mul_cycle, hU, one_mul, Matrix.trace_diagonal]
  · have hsq : G * G = U * (L * L) * star U := by
      rw [hrepr]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U, hU, one_mul]
    rw [hsq, Matrix.trace_mul_cycle, hU, one_mul]
    simp [L, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

abbrev SignMatrix (n : ℕ) := Matrix (Fin n) (Fin n) Bool

noncomputable def integerMatrix {n : ℕ} (A : SignMatrix n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if A i j then 1 else -1

noncomputable def realMatrix {n : ℕ} (A : SignMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => integerMatrix A i j

noncomputable def gram {n : ℕ} (A : SignMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  realMatrix A * (realMatrix A)ᵀ

theorem gram_psd {n : ℕ} (A : SignMatrix n) : (gram A).PosSemidef := by
  simpa [gram] using Matrix.posSemidef_self_mul_conjTranspose (realMatrix A)

theorem gram_diag {n : ℕ} (A : SignMatrix n) (i : Fin n) : gram A i i = n := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, realMatrix]
  have hterm (j : Fin n) : (integerMatrix A i j : ℝ) * integerMatrix A i j = 1 := by
    simp only [integerMatrix]
    split <;> norm_num
  simp [hterm]

theorem gram_symmetric {n : ℕ} (A : SignMatrix n) (i j : Fin n) :
    gram A i j = gram A j i := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every odd-length scalar product of sign vectors is an odd integer. -/
theorem gram_odd_integer {n : ℕ} (A : SignMatrix n) (hn : Odd n) (i j : Fin n) :
    ∃ z : ℤ, Odd z ∧ gram A i j = z := by
  let z : ℤ := ∑ k, integerMatrix A i k * integerMatrix A j k
  have hmod : z % 2 = (n : ℤ) % 2 := by
    dsimp [z]
    rw [Finset.sum_int_mod]
    have hterm (k : Fin n) : (integerMatrix A i k * integerMatrix A j k) % 2 = 1 := by
      simp only [integerMatrix]
      split <;> split <;> norm_num
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  refine ⟨z, ?_, ?_⟩
  · rw [Int.odd_iff, hmod]
    exact_mod_cast Nat.odd_iff.mp hn
  · simp [gram, Matrix.mul_apply, Matrix.transpose_apply, realMatrix, z]

theorem gram_entry_sq_lower {n : ℕ} (A : SignMatrix n) (hn : Odd n) (i j : Fin n) :
    (1 : ℝ) ≤ gram A i j ^ 2 := by
  obtain ⟨z, hz, hzij⟩ := gram_odd_integer A hn i j
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hsq : (1 : ℤ) ≤ z ^ 2 := by
    have hp : 0 < z ^ 2 := sq_pos_of_ne_zero hz0
    omega
  rw [hzij]
  exact_mod_cast hsq

theorem gram_trace {n : ℕ} (A : SignMatrix n) : (gram A).trace = (n : ℝ) ^ 2 := by
  simp [Matrix.trace, Matrix.diag, gram_diag, pow_two]

theorem gram_square_trace_lower {n : ℕ} (A : SignMatrix n) (hn : Odd n) :
    (n : ℝ) * ((n : ℝ) ^ 2 + n - 1) ≤ (gram A * gram A).trace := by
  have hrow (i : Fin n) : (n : ℝ) ^ 2 + n - 1 ≤ ∑ j, (gram A i j) ^ 2 := by
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun j => (gram A i j) ^ 2 - 1)
      (fun j _ => sub_nonneg.mpr (gram_entry_sq_lower A hn i j)) (Finset.mem_univ i)
    simp only [gram_diag, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hrow i)
  have htrace : (gram A * gram A).trace = ∑ i, ∑ j, (gram A i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [gram_symmetric A j i, pow_two]
  rw [htrace]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

/-- Odd orders at least two have a fixed gap in the squared normalized determinant. -/
theorem sign_determinant_gap {n : ℕ} (A : SignMatrix n) (hn : Odd n) (hn2 : 2 ≤ n) :
    (realMatrix A).det ^ 2 / (n : ℝ) ^ n ≤ Real.exp (-(1 / 18 : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let hG := gram_psd A
  let x : Fin n → ℝ := fun i => hG.1.eigenvalues i / n
  obtain ⟨hm1, hm2⟩ := spectral_moments (gram A) hG.1
  have hsum : ∑ i, x i = n := by
    simp only [x, ← Finset.sum_div, hm1, gram_trace]
    field_simp
    ring
  have hvar : (1 : ℝ) / 2 ≤ ∑ i, (x i - 1) ^ 2 := by
    have hid (i : Fin n) : (x i - 1) ^ 2 =
        (hG.1.eigenvalues i) ^ 2 / (n : ℝ) ^ 2 - 2 * x i + 1 := by
      dsimp [x]
      ring
    have heq : (∑ i, (x i - 1) ^ 2) =
        (gram A * gram A).trace / (n : ℝ) ^ 2 - n := by
      simp_rw [hid]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
        ← Finset.mul_sum, hm2, hsum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    rw [heq]
    have ht := gram_square_trace_lower A hn
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rw [le_sub_iff_add_le]
    apply (le_div_iff₀ (sq_pos_of_pos hnpos)).mpr
    nlinarith [mul_nonneg hnpos.le (sub_nonneg.mpr hn2r)]
  have hprod := product_gap x (fun i => div_nonneg (hG.eigenvalues_nonneg i) hnpos.le) hsum hvar
  have heq : (∏ i, x i) = (realMatrix A).det ^ 2 / (n : ℝ) ^ n := by
    have hdet : (gram A).det = ∏ i, hG.1.eigenvalues i := by
      simpa using hG.1.det_eq_prod_eigenvalues
    simp only [x, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← hdet, gram, Matrix.det_mul, Matrix.det_transpose, pow_two]
  rwa [heq] at hprod

/-- The ordinary entrywise sign condition on an arbitrary real matrix. -/
def IsSignMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

theorem realMatrix_isSignMatrix {n : ℕ} (A : SignMatrix n) : IsSignMatrix (realMatrix A) := by
  intro i j
  simp only [realMatrix, integerMatrix]
  split <;> norm_num

/-- Boolean encoding covers every real matrix with entries in {−1,1}. -/
theorem sign_encoding_complete {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsSignMatrix B) : ∃ A : SignMatrix n, realMatrix A = B := by
  classical
  refine ⟨fun i j => decide (B i j = 1), ?_⟩
  ext i j
  by_cases h : B i j = 1
  · simp [realMatrix, integerMatrix, h]
  · have hneg := (hB i j).resolve_left h
    norm_num [realMatrix, integerMatrix, h, hneg]

/-- The maximum absolute determinant over the entire finite sign-matrix class. -/
noncomputable def D (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun A : SignMatrix n => |(realMatrix A).det|)

theorem D_attained (n : ℕ) : ∃ A : SignMatrix n, D n = |(realMatrix A).det| := by
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun A : SignMatrix n => |(realMatrix A).det|)
  exact ⟨A, hA⟩

theorem determinant_le_D {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsSignMatrix B) :
    |B.det| ≤ D n := by
  obtain ⟨A, rfl⟩ := sign_encoding_complete B hB
  exact Finset.le_sup' (fun A : SignMatrix n => |(realMatrix A).det|) (Finset.mem_univ A)

/-- This identifies D with the source's actual maximum, including attainment. -/
theorem D_isMaximum (n : ℕ) :
    (∃ B : Matrix (Fin n) (Fin n) ℝ, IsSignMatrix B ∧ |B.det| = D n) ∧
    (∀ B : Matrix (Fin n) (Fin n) ℝ, IsSignMatrix B → |B.det| ≤ D n) := by
  obtain ⟨A, hA⟩ := D_attained n
  exact ⟨⟨realMatrix A, realMatrix_isSignMatrix A, hA.symm⟩,
    fun B hB => determinant_le_D B hB⟩

/-- Standard real Hadamard matrices: sign entries and orthogonal rows of squared length n. -/
def IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsSignMatrix H ∧ H * Hᵀ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The matrix equation is exactly the usual row-dot-product condition. -/
theorem isHadamard_iff_rows {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard H ↔ IsSignMatrix H ∧
      ∀ i j, (∑ k, H i k * H j k) = if i = j then (n : ℝ) else 0 := by
  constructor
  · rintro ⟨hSign, hM⟩
    refine ⟨hSign, fun i j => ?_⟩
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hM
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_ite] using h
  · rintro ⟨hSign, hrows⟩
    refine ⟨hSign, ?_⟩
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_ite] using hrows i j

/-- Clause (i), over positive integer orders divisible by four. -/
def HadamardConjecture : Prop :=
  ∀ n : ℕ, 0 < n → 4 ∣ n → ∃ H : Matrix (Fin n) (Fin n) ℝ, IsHadamard H

/-- The exponent is real division, with its exact half-integer value for odd n. -/
noncomputable def normalizedMaximum (n : ℕ) : ℝ := D n / (n : ℝ) ^ ((n : ℝ) / 2)

/-- Clause (ii), along all integer orders. The index zero is an irrelevant finite extension. -/
def AllOrdersLimit : Prop := Filter.Tendsto normalizedMaximum Filter.atTop (nhds 1)

/-- The exact full source assertion is the conjunction of both clauses. -/
def OriginalConjecture : Prop := HadamardConjecture ∧ AllOrdersLimit

/-- The filter limit is precisely the usual positive-index epsilon-N statement. -/
theorem allOrdersLimit_iff_positive_epsilon : AllOrdersLimit ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → |normalizedMaximum n - 1| < ε := by
  unfold AllOrdersLimit
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N + 1, by omega, fun n hn => ?_⟩
    simpa only [Real.dist_eq] using hN n (by omega)
  · intro h ε hε
    obtain ⟨N, _, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn⟩

theorem normalization_pos {n : ℕ} (hn : 0 < n) :
    0 < (n : ℝ) ^ ((n : ℝ) / 2) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem normalization_square {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
  have hnreal : 0 ≤ (n : ℝ) := (Nat.cast_pos.mpr hn).le
  rw [← Real.rpow_mul_natCast hnreal]
  norm_num only [Nat.cast_ofNat]
  rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]

theorem normalizedMaximum_odd_gap {n : ℕ} (hn : Odd n) (hn2 : 2 ≤ n) :
    normalizedMaximum n ≤ Real.exp (-(1 / 36 : ℝ)) := by
  obtain ⟨A, hA⟩ := D_attained n
  have hnpos : 0 < n := by omega
  have hgap := sign_determinant_gap A hn hn2
  have hsq : (normalizedMaximum n) ^ 2 ≤ Real.exp (-(1 / 18 : ℝ)) := by
    simpa only [normalizedMaximum, hA, div_pow, normalization_square hnpos, sq_abs] using hgap
  have heq : Real.exp (-(1 / 36 : ℝ)) ^ 2 = Real.exp (-(1 / 18 : ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos := Real.exp_pos (-(1 / 36 : ℝ))
  nlinarith

/-- Clause (ii) is false; arbitrarily large odd orders retain a uniform gap from one. -/
theorem not_AllOrdersLimit : ¬ AllOrdersLimit := by
  intro h
  have hc : Real.exp (-(1 / 36 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hevent := (tendsto_order.mp h).1 _ hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  have hn : Odd (2 * N + 3) := Nat.odd_iff.mpr (by omega)
  have hlarge := hN (2 * N + 3) (by omega)
  have hgap := normalizedMaximum_odd_gap hn (by omega)
  exact (not_lt_of_ge hgap) hlarge

/-- The actual negation of the entire original conjunction. -/
theorem conjecture236_false : ¬ OriginalConjecture := by
  intro h
  exact not_AllOrdersLimit h.2

end Conjecture236
