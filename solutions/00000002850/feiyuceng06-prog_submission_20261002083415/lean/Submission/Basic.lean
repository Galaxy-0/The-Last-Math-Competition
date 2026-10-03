import Mathlib

/-!
# Conjecture 00000002850 is false

The *nonnegative rank* of an entrywise nonnegative real matrix `M` is the least `k`
such that `M = W H` with `W` (`m × k`) and `H` (`k × n`) entrywise nonnegative. It is
at least the ordinary rank. Conjecture 00000002850 asserts that the separation of
the nonnegative rank from the ordinary rank "starts at rank 4", that is, the
smallest rank at which a nonnegative matrix can have strictly larger nonnegative
rank is `4`.

It already happens at rank `3`. The slack matrix of a square,

  `S = [[1,1,0,0], [0,1,1,0], [0,0,1,1], [1,0,0,1]]`,

has rank `3` (its fourth row is `r₁ - r₂ + r₃`, and the leading `3 × 3` block is
invertible) but nonnegative rank `4`. The argument for the last claim is a fooling
set. In a nonnegative factorization `S = ∑ₖ wₖ hₖᵀ` with `K` terms, each diagonal
entry `S i i = 1` needs a term `k` with `wₖ i > 0` and `hₖ i > 0`. Two diagonal
positions `i ≠ j` cannot share a term, since that term would make both `S i j`
and `S j i` positive, while for every `i ≠ j` one of them is `0`. So the four
diagonal positions need four different terms, and `K ≥ 4`.
-/

namespace Submission00000002850

open Matrix

/-- `M` has a nonnegative factorization of inner dimension `k`: `M = W * H` with `W`
(`m × k`) and `H` (`k × n`) entrywise nonnegative. The nonnegative rank of `M` is the
least such `k`. -/
def HasNonnegFactorization {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Prop :=
  ∃ (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ),
    (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧ W * H = M

/-- Nonnegative rank separates from ordinary rank at rank `r`: some entrywise
nonnegative real matrix of rank `r` has nonnegative rank larger than `r`. -/
def SeparatesAt (r : ℕ) : Prop :=
  ∃ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ),
    (∀ i j, 0 ≤ M i j) ∧ M.rank = r ∧ ¬ HasNonnegFactorization M r

/-- Conjecture 00000002850: the separation of nonnegative rank from ordinary rank
starts at rank `4`; it occurs at rank `4` and at no smaller rank. -/
def ConjectureHolds : Prop := SeparatesAt 4 ∧ ∀ r < 4, ¬ SeparatesAt r

/-- The slack matrix of a square. -/
def S : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 0, 0;
     0, 1, 1, 0;
     0, 0, 1, 1;
     1, 0, 0, 1]

theorem S_nonneg (i j : Fin 4) : 0 ≤ S i j := by
  fin_cases i <;> fin_cases j <;> simp [S]

/-- `S` has rank `3`. -/
theorem rank_S : S.rank = 3 := by
  apply le_antisymm
  · -- `S = A * B` with inner dimension `3`: the fourth row is `r₁ - r₂ + r₃`.
    have h : S = (!![1, 0, 0; 0, 1, 0; 0, 0, 1; 1, -1, 1] : Matrix (Fin 4) (Fin 3) ℝ) *
        (!![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1] : Matrix (Fin 3) (Fin 4) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [h]
    exact (rank_mul_le_left _ _).trans (rank_le_width _)
  · -- The leading `3 × 3` block is invertible.
    have hN : (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] : Matrix (Fin 3) (Fin 4) ℝ) * S *
        (!![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 4) (Fin 3) ℝ) =
        !![1, 1, 0; 0, 1, 1; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_succ]
    have hunit : IsUnit (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simp [Matrix.det_fin_three]
    have h3 := rank_of_isUnit _ hunit
    rw [Fintype.card_fin, ← hN] at h3
    rw [← h3]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- Off the diagonal, `S i j` and `S j i` are never both positive. -/
theorem S_fooling (i j : Fin 4) (hij : i ≠ j) : S i j = 0 ∨ S j i = 0 := by
  fin_cases i <;> fin_cases j <;> simp [S] at hij ⊢

theorem S_diag (i : Fin 4) : S i i = 1 := by
  fin_cases i <;> simp [S]

/-- `S` has no nonnegative factorization of inner dimension `3`. -/
theorem not_hasNonnegFactorization_S : ¬ HasNonnegFactorization S 3 := by
  rintro ⟨W, H, hW, hH, hWH⟩
  have hentry : ∀ i j, S i j = ∑ k, W i k * H k j := fun i j => by
    rw [← hWH, Matrix.mul_apply]
  -- Each diagonal entry needs a term that is positive there.
  have hpos : ∀ i, ∃ k, 0 < W i k ∧ 0 < H k i := by
    intro i
    by_contra hne
    push Not at hne
    have hzero : ∑ k, W i k * H k i = 0 := Finset.sum_eq_zero fun k _ => by
      rcases (hW i k).lt_or_eq with h | h
      · rw [le_antisymm (hne k h) (hH k i), mul_zero]
      · rw [← h, zero_mul]
    have hd := S_diag i
    rw [hentry, hzero] at hd
    norm_num at hd
  choose f hf using hpos
  -- A single term bounds an entry from below.
  have hge : ∀ i j k, W i k * H k j ≤ S i j := fun i j k => by
    rw [hentry]
    exact Finset.single_le_sum (f := fun k => W i k * H k j)
      (fun k _ => mul_nonneg (hW i k) (hH k j)) (Finset.mem_univ k)
  -- Distinct diagonal positions use distinct terms.
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases S_fooling i j hne with h | h
    · have h1 := hge i j (f i)
      have h2 : 0 < W i (f i) * H (f i) j := mul_pos (hf i).1 (by rw [hij]; exact (hf j).2)
      linarith
    · have h1 := hge j i (f j)
      have h2 : 0 < W j (f j) * H (f j) i := mul_pos (hf j).1 (by rw [← hij]; exact (hf i).2)
      linarith
  have := Fintype.card_le_of_injective f hinj
  simp at this

/-- Nonnegative rank separates from rank already at rank `3`. -/
theorem separatesAt_three : SeparatesAt 3 :=
  ⟨4, 4, S, S_nonneg, rank_S, not_hasNonnegFactorization_S⟩

/-- Conjecture 00000002850 is false: the separation already occurs at rank `3`. -/
theorem conjecture_00000002850_false : ¬ ConjectureHolds :=
  fun h => h.2 3 (by norm_num) separatesAt_three

end Submission00000002850

#print axioms Submission00000002850.conjecture_00000002850_false
