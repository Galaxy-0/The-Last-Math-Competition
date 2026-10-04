import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Conjecture360

/-- The actual product of the linear forms represented by A, at an integer point. -/
noncomputable def productAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℤ) : ℝ :=
  ∏ i, (A.mulVec (fun j => (x j : ℝ))) i

/-- A constant works uniformly for all real diagonal systems, including singular ones. -/
def uniformDiagonalBound (n : ℕ) (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      |productAt (Matrix.diagonal a) x| ≤ c * |Matrix.det (Matrix.diagonal a)|

/-- The same bound restricted to nonsingular diagonal systems. -/
def uniformNonsingularDiagonalBound (n : ℕ) (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ, (∀ i, a i ≠ 0) →
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      |productAt (Matrix.diagonal a) x| ≤ c * |Matrix.det (Matrix.diagonal a)|

/-- The first coordinate vector, an admissible nonzero integer point in every dimension ≥ 2. -/
def firstCoordinate (n : ℕ) : Fin (n + 2) → ℤ :=
  fun i => if i.val = 0 then 1 else 0

theorem firstCoordinate_ne_zero (n : ℕ) : firstCoordinate n ≠ 0 := by
  intro h
  have hzero := congrFun h ⟨0, by omega⟩
  norm_num [firstCoordinate] at hzero

/-- The explicit nonzero-coefficient restriction implies actual nonzero determinant. -/
theorem diagonal_det_ne_zero {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    Matrix.det (Matrix.diagonal a) ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)

/-- The second form vanishes at the first coordinate vector. -/
theorem diagonal_product_firstCoordinate (n : ℕ) (a : Fin (n + 2) → ℝ) :
    productAt (Matrix.diagonal a) (firstCoordinate n) = 0 := by
  unfold productAt
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨1, by omega⟩ : Fin (n + 2)))
  simp [Matrix.mulVec_diagonal, firstCoordinate]

/-- This point globally minimizes the absolute product, even among all integer points. -/
theorem firstCoordinate_global_minimum (n : ℕ) (a : Fin (n + 2) → ℝ)
    (x : Fin (n + 2) → ℤ) :
    |productAt (Matrix.diagonal a) (firstCoordinate n)| ≤
      |productAt (Matrix.diagonal a) x| := by
  rw [diagonal_product_firstCoordinate, abs_zero]
  exact abs_nonneg _

/-- A uniform diagonal bound exists exactly for the nonnegative constants. -/
theorem uniformDiagonalBound_iff (n : ℕ) (c : ℝ) :
    uniformDiagonalBound (n + 2) c ↔ 0 ≤ c := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := h (fun _ => 1)
    have hnonneg := (abs_nonneg (productAt (Matrix.diagonal (fun _ : Fin (n + 2) => 1)) x)).trans hx
    simpa using hnonneg
  · intro hc a
    refine ⟨firstCoordinate n, firstCoordinate_ne_zero n, ?_⟩
    rw [diagonal_product_firstCoordinate, abs_zero]
    exact mul_nonneg hc (abs_nonneg _)

/-- The sharp-constant conclusion also holds on the nonsingular subclass. -/
theorem uniformNonsingularDiagonalBound_iff (n : ℕ) (c : ℝ) :
    uniformNonsingularDiagonalBound (n + 2) c ↔ 0 ≤ c := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := h (fun _ => 1) (by intro i; norm_num)
    have hnonneg := (abs_nonneg (productAt (Matrix.diagonal (fun _ : Fin (n + 2) => 1)) x)).trans hx
    simpa using hnonneg
  · intro hc a _
    exact (uniformDiagonalBound_iff n c).mpr hc a

/-- Optimality means the bound holds and no strictly smaller nonnegative bound holds. -/
def optimalDiagonalConstant (n : ℕ) (c : ℝ) : Prop :=
  uniformDiagonalBound n c ∧
    ¬∃ d : ℝ, 0 ≤ d ∧ d < c ∧ uniformDiagonalBound n d

/-- Zero is the actual sharp constant for all these diagonal systems. -/
theorem zero_is_optimal (n : ℕ) : optimalDiagonalConstant (n + 2) 0 := by
  refine ⟨(uniformDiagonalBound_iff n 0).mpr le_rfl, ?_⟩
  rintro ⟨d, hd, hlt, _⟩
  exact (not_lt_of_ge hd) hlt

/-- The numerical constant explicitly asserted to be unimprovable at n = 10. -/
noncomputable def claimedConstant : ℝ := (Nat.factorial 10 : ℝ) / (10 : ℝ) ^ 10

theorem claimedConstant_pos : 0 < claimedConstant := by
  norm_num [claimedConstant]

/-- The conjecture's exact constant is a valid, but non-optimal, bound. -/
theorem claimedConstant_is_bound : uniformDiagonalBound 10 claimedConstant := by
  exact (uniformDiagonalBound_iff 8 claimedConstant).mpr claimedConstant_pos.le

/-- There is a strictly better positive constant, so restricting to positive constants does not help. -/
theorem positive_improvement :
    0 < claimedConstant / 2 ∧ claimedConstant / 2 < claimedConstant ∧
      uniformDiagonalBound 10 (claimedConstant / 2) := by
  have hpos := claimedConstant_pos
  refine ⟨by positivity, by linarith, ?_⟩
  exact (uniformDiagonalBound_iff 8 _).mpr (by positivity)

/-- The exact first assertion of the stated conjecture. -/
def optimalityClaim : Prop := optimalDiagonalConstant 10 claimedConstant

theorem not_optimalityClaim : ¬optimalityClaim := by
  rintro ⟨_, hsharp⟩
  exact hsharp ⟨claimedConstant / 2, positive_improvement.1.le,
    positive_improvement.2.1, positive_improvement.2.2⟩

/-- The conjectured optimality assertion is false. -/
theorem conjecture360_disproof : ¬optimalityClaim := not_optimalityClaim

end Conjecture360
