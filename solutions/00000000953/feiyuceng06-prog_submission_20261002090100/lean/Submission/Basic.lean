import Mathlib

/-!
# Conjecture 00000000953 holds

A *real equiangular tight frame* (ETF) of `N` vectors in `ℝ^d` consists of unit vectors
`f₁, …, f_N` with `|⟪fᵢ, fⱼ⟫| = α` for all `i ≠ j` (equiangular) and
`∑ᵢ ⟪fᵢ, x⟫ fᵢ = A x` for all `x` (tight). Conjecture 00000000953 asserts that a real
ETF of `17` vectors in `ℝ⁸` does not exist, while one of `16` vectors in `ℝ⁶` does.

**Nonexistence of ETF(17, 8).** Let `G = (⟪fᵢ, fⱼ⟫)` be the Gram matrix.

* Tightness gives `G² = A G`, and taking the trace in an orthonormal basis gives
  `A · 8 = 17`.
* The diagonal of `G² = A G` reads `1 + 16 α² = A = 17/8`, so `α² = 9/128`.
* Off the diagonal, `(G²)ᵢⱼ = 2 Gᵢⱼ + ∑_{k ≠ i, j} Gᵢₖ Gₖⱼ`, and each product `Gᵢₖ Gₖⱼ`
  is `±α²`. So `(A - 2) Gᵢⱼ = α² m` for an integer `m`, i.e. `Gᵢⱼ = (9/16) m`.
* Squaring gives `9/128 = α² = (81/256) m²`, i.e. `9 m² = 2`, which is impossible.

**Existence of ETF(16, 6).** Take the `16` sign vectors `(1, x₂, …, x₆) ∈ {±1}⁶` with
`x₂ x₃ x₄ x₅ x₆ = 1`, divided by `√6`. Distinct ones have inner product `±2/6 = ±1/3`,
and `∑ᵢ vᵢ vᵢᵀ = 16 I`, so the frame is tight with `A = 16/6`.
-/

namespace Submission00000000953

open Finset

/-- A real equiangular tight frame of `N` vectors in `ℝ^d`: unit vectors, all pairwise
inner products of the same absolute value `α`, and frame operator `x ↦ ∑ᵢ ⟪fᵢ, x⟫ fᵢ`
equal to a multiple `A • x` of the identity. -/
def IsETF (N d : ℕ) (f : Fin N → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, ‖f i‖ = 1) ∧ (∃ α : ℝ, ∀ i j, i ≠ j → |inner ℝ (f i) (f j)| = α) ∧
    ∃ A : ℝ, ∀ x, ∑ i, inner ℝ (f i) x • f i = A • x

/-- A real ETF of `N` vectors in `ℝ^d` exists. -/
def ETFExists (N d : ℕ) : Prop := ∃ f : Fin N → EuclideanSpace ℝ (Fin d), IsETF N d f

/-- Conjecture 00000000953: the real ETF(17, 8) does not exist, while ETF(16, 6) does. -/
def ConjectureHolds : Prop := ¬ ETFExists 17 8 ∧ ETFExists 16 6

/-! ## General facts about tight frames -/

section Frames

variable {N d : ℕ} {f : Fin N → EuclideanSpace ℝ (Fin d)} {A : ℝ}

/-- Tightness gives `G² = A G` for the Gram matrix. -/
theorem gram_sq (hA : ∀ x, ∑ i, inner ℝ (f i) x • f i = A • x) (i j : Fin N) :
    ∑ k, inner ℝ (f i) (f k) * inner ℝ (f k) (f j) = A * inner ℝ (f i) (f j) := by
  have := congrArg (inner ℝ (f i)) (hA (f j))
  rw [inner_sum, inner_smul_right] at this
  simp only [inner_smul_right] at this
  rw [← this]
  exact sum_congr rfl fun k _ => mul_comm _ _

/-- The trace of the frame operator: `A · d = N` for a tight frame of unit vectors. -/
theorem trace_eq (hnorm : ∀ i, ‖f i‖ = 1) (hA : ∀ x, ∑ i, inner ℝ (f i) x • f i = A • x) :
    A * d = N := by
  set e := EuclideanSpace.basisFun (Fin d) ℝ
  have h1 : ∑ k, inner ℝ (e k) (∑ i, inner ℝ (f i) (e k) • f i) = A * d := by
    simp_rw [hA, inner_smul_right, real_inner_self_eq_norm_sq, e.norm_eq_one]
    simp [mul_comm]
  have h2 : ∑ k, inner ℝ (e k) (∑ i, inner ℝ (f i) (e k) • f i) = N := by
    simp_rw [inner_sum, inner_smul_right]
    rw [sum_comm]
    have : ∀ i, ∑ k, inner ℝ (f i) (e k) * inner ℝ (e k) (f i) = 1 := by
      intro i
      rw [e.sum_inner_mul_inner, real_inner_self_eq_norm_sq, hnorm i, one_pow]
    simp_rw [mul_comm (inner ℝ (f _) (e _)) _] at this ⊢
    simp_rw [real_inner_comm (e _) (f _)] at this ⊢
    simp [this]
  rw [← h1, h2]

end Frames

/-! ## ETF(17, 8) does not exist -/

theorem not_etf_17_8 : ¬ ETFExists 17 8 := by
  rintro ⟨f, hnorm, ⟨α, hα⟩, A, hA⟩
  set G : Fin 17 → Fin 17 → ℝ := fun i j => inner ℝ (f i) (f j) with hG
  have hGsymm : ∀ i j, G i j = G j i := fun i j => real_inner_comm _ _
  have hGdiag : ∀ i, G i i = 1 := fun i => by
    simp [hG, hnorm i]
  have hGsq : ∀ i j, i ≠ j → G i j ^ 2 = α ^ 2 := fun i j hij => by
    rw [← hα i j hij, sq_abs]
  -- the trace: `A = 17/8`
  have htr := trace_eq hnorm hA
  push_cast at htr
  have hA' : A = 17 / 8 := by linarith
  -- the diagonal entry `(0,0)` of `G² = A G`: `A = 1 + 16 α²`
  have hdiag := gram_sq hA 0 0
  have hdiag' : ∑ k, G 0 k * G k 0 = 1 + 16 * α ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp only [hGdiag, mul_one]
    have : ∀ k : Fin 16, G 0 k.succ * G k.succ 0 = α ^ 2 := fun k => by
      rw [hGsymm k.succ 0, ← sq, hGsq 0 k.succ (Fin.succ_ne_zero k).symm]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hα2 : α ^ 2 = 9 / 128 := by
    have h : ∑ k, G 0 k * G k 0 = A * G 0 0 := hdiag
    rw [hdiag', hGdiag, hA'] at h
    linarith
  -- each off-diagonal product `G 0 k * G k 1` with `k ≠ 0, 1` is `±α²`
  set s : Finset (Fin 17) := univ.filter fun k => k ≠ 0 ∧ k ≠ 1 with hs
  have hpm : ∀ k ∈ s, ∃ e : ℤ, G 0 k * G k 1 = α ^ 2 * e := by
    intro k hk
    simp only [hs, mem_filter, mem_univ, true_and] at hk
    have hsq : (G 0 k * G k 1) ^ 2 = (α ^ 2) ^ 2 := by
      rw [mul_pow, hGsq 0 k (Ne.symm hk.1), hGsq k 1 hk.2]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨1, by rw [h]; push_cast; ring⟩
    · exact ⟨-1, by rw [h]; push_cast; ring⟩
  choose! e he using hpm
  set m : ℤ := ∑ k ∈ s, e k with hm
  -- the off-diagonal entry `(0, 1)` of `G² = A G`
  have hoff : ∑ k, G 0 k * G k 1 = A * G 0 1 := gram_sq hA 0 1
  have hoff' : ∑ k, G 0 k * G k 1 = 2 * G 0 1 + α ^ 2 * m := by
    have hsplit : (univ : Finset (Fin 17)) = insert 0 (insert 1 s) := by
      ext k
      simp only [hs, mem_univ, mem_insert, mem_filter, true_and]
      tauto
    rw [hsplit, sum_insert (by simp [hs]), sum_insert (by simp [hs]), hGdiag 0, hGdiag 1,
      sum_congr rfl he, ← mul_sum, hm]
    push_cast
    ring
  have hG01 : G 0 1 = 9 / 16 * m := by
    rw [hoff', hA', hα2] at hoff
    linarith
  have hsq01 := hGsq 0 1 (by decide)
  rw [hG01, hα2] at hsq01
  have h9 : (9 : ℝ) * (m : ℝ) ^ 2 = 2 := by nlinarith
  have h9' : (9 : ℤ) * m ^ 2 = 2 := by exact_mod_cast h9
  have h92 : (9 : ℤ) ∣ 2 := ⟨m ^ 2, by linarith⟩
  norm_num at h92

/-! ## ETF(16, 6) exists -/

/-- The `16` sign vectors `(1, x₂, …, x₆) ∈ {±1}⁶` with `x₂ x₃ x₄ x₅ x₆ = 1`. -/
def v : Fin 16 → Fin 6 → ℤ :=
  ![![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, -1, -1],
    ![1, 1, 1, -1, 1, -1],
    ![1, 1, 1, -1, -1, 1],
    ![1, 1, -1, 1, 1, -1],
    ![1, 1, -1, 1, -1, 1],
    ![1, 1, -1, -1, 1, 1],
    ![1, 1, -1, -1, -1, -1],
    ![1, -1, 1, 1, 1, -1],
    ![1, -1, 1, 1, -1, 1],
    ![1, -1, 1, -1, 1, 1],
    ![1, -1, 1, -1, -1, -1],
    ![1, -1, -1, 1, 1, 1],
    ![1, -1, -1, 1, -1, -1],
    ![1, -1, -1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1]]

/-- Distinct vectors have inner product `±2`. -/
theorem v_gram : ∀ i j : Fin 16, i ≠ j →
    (∑ l, v i l * v j l = 2 ∨ ∑ l, v i l * v j l = -2) := by
  decide

theorem v_norm : ∀ i : Fin 16, ∑ l, v i l * v i l = 6 := by
  decide

/-- `∑ᵢ vᵢ vᵢᵀ = 16 I`. -/
theorem v_frame : ∀ k l : Fin 6, ∑ i, v i k * v i l = if k = l then 16 else 0 := by
  decide

/-- The frame vectors `vᵢ / √6 ∈ ℝ⁶`. -/
noncomputable def F (i : Fin 16) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 fun l => (v i l : ℝ) / Real.sqrt 6

theorem F_apply (i : Fin 16) (l : Fin 6) : F i l = (v i l : ℝ) / Real.sqrt 6 := rfl

theorem sqrt6_mul_self : Real.sqrt 6 * Real.sqrt 6 = 6 :=
  Real.mul_self_sqrt (by norm_num)

theorem inner_F (i j : Fin 16) :
    inner ℝ (F i) (F j) = ((∑ l, v i l * v j l : ℤ) : ℝ) / 6 := by
  simp only [F, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun l _ => ?_
  rw [div_mul_div_comm, sqrt6_mul_self, mul_comm]

theorem norm_F (i : Fin 16) : ‖F i‖ = 1 := by
  have h : ‖F i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_F, v_norm]
    norm_num
  rw [← Real.sqrt_sq (norm_nonneg (F i)), h, Real.sqrt_one]

theorem abs_inner_F {i j : Fin 16} (hij : i ≠ j) : |inner ℝ (F i) (F j)| = 1 / 3 := by
  rw [inner_F]
  rcases v_gram i j hij with h | h <;> rw [h] <;> norm_num [abs_div]

theorem tight_F (x : EuclideanSpace ℝ (Fin 6)) :
    ∑ i, inner ℝ (F i) x • F i = (8 / 3 : ℝ) • x := by
  have hinv : (Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹ = (6 : ℝ)⁻¹ := by
    rw [← mul_inv, sqrt6_mul_self]
  have hcast : ∀ m l : Fin 6, (∑ i, (v i m : ℝ) * (v i l : ℝ)) = if m = l then 16 else 0 := by
    intro m l
    have h2 : (∑ i, (v i m : ℝ) * (v i l : ℝ)) = ((∑ i, v i m * v i l : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [h2, v_frame m l]
    split_ifs <;> norm_num
  ext l
  have hterm : ∀ i, inner ℝ (F i) x * F i l =
      ∑ m, x m * ((v i m : ℝ) * (v i l : ℝ)) * (6 : ℝ)⁻¹ := by
    intro i
    simp only [F_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hinv]
    ring
  calc (∑ i, inner ℝ (F i) x • F i) l = ∑ i, inner ℝ (F i) x * F i l := by simp
    _ = ∑ i, ∑ m, x m * ((v i m : ℝ) * (v i l : ℝ)) * (6 : ℝ)⁻¹ :=
        sum_congr rfl fun i _ => hterm i
    _ = ∑ m, x m * (∑ i, (v i m : ℝ) * (v i l : ℝ)) * (6 : ℝ)⁻¹ := by
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum, sum_mul]
    _ = ∑ m, x m * (if m = l then 16 else 0) * (6 : ℝ)⁻¹ := by simp_rw [hcast]
    _ = ((8 / 3 : ℝ) • x) l := by
        simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
        simp
        ring

theorem etf_16_6 : ETFExists 16 6 :=
  ⟨F, norm_F, ⟨1 / 3, fun _ _ h => abs_inner_F h⟩, ⟨8 / 3, tight_F⟩⟩

/-- Conjecture 00000000953 holds. -/
theorem conjecture_00000000953 : ConjectureHolds := ⟨not_etf_17_8, etf_16_6⟩

end Submission00000000953

#print axioms Submission00000000953.conjecture_00000000953
