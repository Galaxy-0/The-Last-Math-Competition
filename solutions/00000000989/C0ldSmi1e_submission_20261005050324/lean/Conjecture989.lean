import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

/-!
# Conjecture 00000000989: the positive-map convention

Here dimension means matrix side length: maps are complex-linear maps M_d(C) -> M_d(C).
Positive matrices are Hermitian positive-semidefinite matrices, and complete positivity
means positivity of every positive finite block ampliation. Decomposable has its standard
positive-map meaning P = S + transpose o T, with S and T completely positive and with zero
summands allowed. It does not mean an extreme ray, a convex extreme point, or absence of
invariant direct-sum blocks. Choi rank is the complex rank of the unnormalized Choi matrix.

Every completely positive map is decomposable. Consequently no individual map, and hence
no nonempty family of maps, can satisfy the conjecture under these conventions. The proof
holds in all dimensions, so the missing lower cutoff in the question is immaterial.
-/

namespace Conjecture989

open scoped ComplexOrder Kronecker Matrix

/-- The actual complex matrix algebra with side length d. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Complex-linear maps on the matrix algebra, with the library map operations. -/
abbrev MatrixMap (d : ℕ) := Mat d →ₗ[ℂ] Mat d

/-- The library positivity predicate is Hermitian positivity of complex quadratic forms.
The explicit real/imaginary statement prevents confusion with entrywise positivity. -/
theorem posSemidef_iff_quadratic {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ v : n → ℂ,
      0 ≤ (dotProduct (star v) (A *ᵥ v)).re ∧
      (dotProduct (star v) (A *ᵥ v)).im = 0 := by
  constructor
  · rintro ⟨hH, hQ⟩
    exact ⟨hH, fun v => RCLike.nonneg_iff.mp (hQ v)⟩
  · rintro ⟨hH, hQ⟩
    exact ⟨hH, fun v => RCLike.nonneg_iff.mpr (hQ v)⟩

/-- Positive maps preserve the actual cone of Hermitian positive-semidefinite matrices. -/
def Positive {d : ℕ} (Φ : MatrixMap d) : Prop :=
  ∀ A : Mat d, A.PosSemidef → (Φ A).PosSemidef

/-- Block (a,b), with the block index before the within-block matrix index. -/
noncomputable def block {k d : ℕ}
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) (a b : Fin k) : Mat d :=
  fun i j => X (a, i) (b, j)

/-- The actual complex-linear block ampliation id_k tensor Φ. -/
noncomputable def amplification {d : ℕ} (Φ : MatrixMap d) (k : ℕ) :
    Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ where
  toFun X := fun a b => Φ (block X a.1 b.1) a.2 b.2
  map_add' X Y := by
    ext a b
    exact congrFun (congrFun (Φ.map_add (block X a.1 b.1) (block Y a.1 b.1)) a.2) b.2
  map_smul' c X := by
    ext a b
    exact congrFun (congrFun (Φ.map_smul c (block X a.1 b.1)) a.2) b.2

/-- Entry formula fixing the ampliation's index order. -/
theorem amplification_apply {d k : ℕ} (Φ : MatrixMap d)
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (a b : Fin k) (i j : Fin d) :
    amplification Φ k X (a, i) (b, j) = Φ (block X a b) i j := rfl

/-- On genuine Kronecker products, the ampliation acts as id tensor Φ. -/
theorem amplification_kronecker {d k : ℕ} (Φ : MatrixMap d) (B : Mat k) (A : Mat d) :
    amplification Φ k (B ⊗ₖ A) = B ⊗ₖ (Φ A) := by
  ext a b
  change Φ (B a.1 b.1 • A) a.2 b.2 = B a.1 b.1 * Φ A a.2 b.2
  rw [Φ.map_smul]
  rfl

/-- Every block matrix is a sum of genuine Kronecker products. Together with the previous
lemma and complex linearity, this identifies the ampliation on the entire matrix algebra. -/
theorem block_kronecker_expansion {d k : ℕ}
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) :
    X = ∑ a : Fin k, ∑ b : Fin k,
      (Matrix.stdBasisMatrix a b (1 : ℂ)) ⊗ₖ (block X a b) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.kroneckerMap, Matrix.stdBasisMatrix, block, ite_and]

/-- Complete positivity quantifies over all positive finite matrix sizes. -/
def CompletelyPositive {d : ℕ} (Φ : MatrixMap d) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ,
    X.PosSemidef → (amplification Φ k X).PosSemidef

/-- Amplifying the zero linear map gives the zero linear map. -/
theorem amplification_zero (d k : ℕ) :
    amplification (0 : MatrixMap d) k = 0 := by
  ext X a b
  rfl

/-- The zero map is completely positive because each of its outputs is the PSD zero matrix. -/
theorem zero_completelyPositive (d : ℕ) : CompletelyPositive (0 : MatrixMap d) := by
  intro k _ X _
  rw [amplification_zero]
  exact Matrix.PosSemidef.zero

/-- Complete positivity really implies positivity on the original matrix algebra. -/
theorem CompletelyPositive.positive {d : ℕ} {Φ : MatrixMap d}
    (hΦ : CompletelyPositive Φ) : Positive Φ := by
  intro A hA
  let X : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) ℂ := A.submatrix Prod.snd Prod.snd
  have hX : X.PosSemidef := hA.submatrix Prod.snd
  have hY := hΦ 1 (by decide) X hX
  have hsub := hY.submatrix (fun i : Fin d => ((0 : Fin 1), i))
  change (Φ A).PosSemidef at hsub
  exact hsub

/-- Ordinary matrix transpose as an actual complex-linear map; there is no conjugation. -/
noncomputable def transposeMap (d : ℕ) : MatrixMap d :=
  (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℂ ℂ).toLinearMap

/-- This is the output transpose convention in the definition of decomposability. -/
theorem transposeMap_apply {d : ℕ} (A : Mat d) : transposeMap d A = A.transpose := rfl

/-- Transpose swaps the indices without taking complex conjugates. -/
theorem transposeMap_entry {d : ℕ} (A : Mat d) (i j : Fin d) :
    transposeMap d A i j = A j i := rfl

/-- The decomposition uses the library's actual map sum and actual map composition. -/
theorem decomposition_apply {d : ℕ} (S T : MatrixMap d) (A : Mat d) :
    (S + (transposeMap d).comp T) A = S A + (T A).transpose := rfl

/-- Standard decomposability in the cone of positive maps, using output transpose. -/
def Decomposable {d : ℕ} (Φ : MatrixMap d) : Prop :=
  ∃ S T : MatrixMap d,
    CompletelyPositive S ∧ CompletelyPositive T ∧ Φ = S + (transposeMap d).comp T

/-- Standard indecomposable positive maps, with no normalization or nonzero-summand condition. -/
def Indecomposable {d : ℕ} (Φ : MatrixMap d) : Prop :=
  Positive Φ ∧ ¬ Decomposable Φ

/-- Every CP map has a valid decomposition with the zero second summand. -/
theorem CompletelyPositive.decomposable {d : ℕ} {Φ : MatrixMap d}
    (hΦ : CompletelyPositive Φ) : Decomposable Φ := by
  refine ⟨Φ, 0, hΦ, zero_completelyPositive d, ?_⟩
  simp

/-- The obstruction is uniform and does not depend on any rank or dimension cutoff. -/
theorem not_indecomposable_of_completelyPositive {d : ℕ} {Φ : MatrixMap d}
    (hΦ : CompletelyPositive Φ) : ¬ Indecomposable Φ := by
  intro hI
  exact hI.2 hΦ.decomposable

/-- Standard matrix units E_ij in the fixed coordinate basis. -/
noncomputable def matrixUnit {d : ℕ} (i j : Fin d) : Mat d :=
  Matrix.stdBasisMatrix i j 1

/-- Matrix-unit entries, including the complex value 1. -/
theorem matrixUnit_entry {d : ℕ} (i j a b : Fin d) :
    matrixUnit i j a b = if i = a ∧ j = b then (1 : ℂ) else 0 := rfl

/-- The unnormalized Choi matrix, with input index first and output index second. -/
noncomputable def choiMatrix {d : ℕ} (Φ : MatrixMap d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => Φ (matrixUnit a.1 b.1) a.2 b.2

/-- Standard Choi block formula C_Φ[(i,a),(j,b)] = Φ(E_ij)[a,b]. -/
theorem choiMatrix_entry {d : ℕ} (Φ : MatrixMap d) (i j a b : Fin d) :
    choiMatrix Φ (i, a) (j, b) = Φ (Matrix.stdBasisMatrix i j 1) a b := rfl

/-- Standard unnormalized Choi sum formula. -/
theorem choiMatrix_eq_sum {d : ℕ} (Φ : MatrixMap d) :
    choiMatrix Φ = ∑ i : Fin d, ∑ j : Fin d,
      (matrixUnit i j) ⊗ₖ (Φ (matrixUnit i j)) := by
  ext a b
  simp [choiMatrix, matrixUnit, Matrix.sum_apply, Matrix.kroneckerMap,
    Matrix.stdBasisMatrix, ite_and]

/-- The ordinary complex rank of the genuine Choi matrix, not the rank of Φ itself. -/
noncomputable def choiRank {d : ℕ} (Φ : MatrixMap d) : ℕ := (choiMatrix Φ).rank

/-- Choi rank is complex dimension of the image of multiplication by the Choi matrix. -/
theorem choiRank_eq_finrank {d : ℕ} (Φ : MatrixMap d) :
    choiRank Φ = Module.finrank ℂ (LinearMap.range (choiMatrix Φ).mulVecLin) := rfl

/-- The Choi matrix has d² rows and d² columns. -/
theorem choi_index_card (d : ℕ) : Fintype.card (Fin d × Fin d) = d ^ 2 := by
  simp [pow_two]

/-- Its rank obeys the usual matrix-size bound. This is independent of complete positivity. -/
theorem choiRank_le (d : ℕ) (Φ : MatrixMap d) : choiRank Φ ≤ d ^ 2 := by
  simpa [choiRank, pow_two] using (choiMatrix Φ).rank_le_card_width

/-- In positive dimensions natural-number subtraction is precisely the corank-one condition,
so no truncated subtraction at dimension zero enters the conjecture specialization. -/
theorem rankCondition_iff_corankOne {d : ℕ} (hd : 0 < d) (Φ : MatrixMap d) :
    choiRank Φ = d ^ 2 - 1 ↔ choiRank Φ + 1 = d ^ 2 := by
  have hd2 : 1 ≤ d ^ 2 := Nat.succ_le_of_lt (pow_pos hd 2)
  constructor
  · intro h
    rw [h, Nat.sub_add_cancel hd2]
  · intro h
    exact Nat.eq_sub_of_add_eq h

/-- A conjectured member, under the disclosed positive-dimension square-system convention.
The unexplained word "extremal" adds no condition beyond the explicit numerical rank. -/
def ConjecturedMember (d : ℕ) (Φ : MatrixMap d) : Prop :=
  0 < d ∧ CompletelyPositive Φ ∧ Indecomposable Φ ∧ choiRank Φ = d ^ 2 - 1

/-- No individual map satisfies the original conjunction, including its genuine rank condition. -/
theorem no_conjectured_member (d : ℕ) (Φ : MatrixMap d) : ¬ ConjecturedMember d Φ := by
  rintro ⟨_, hCP, hI, _⟩
  exact not_indecomposable_of_completelyPositive hCP hI

/-- Explicit passage from absence of members to absence of any nonempty family, even with
arbitrary varying positive dimensions. No assumption about computability of the family is needed. -/
theorem no_nonempty_family {I : Type*} [Nonempty I] (d : I → ℕ)
    (Φ : (i : I) → MatrixMap (d i)) : ¬ ∀ i, ConjecturedMember (d i) (Φ i) := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty I›
  exact no_conjectured_member (d i) (Φ i) (h i)

/-- The existential family claim is false. Forbidding all nonempty families also forbids
explicit nonempty families, whatever additional constructive requirement "explicit" intended. -/
theorem conjecture989_false :
    ¬ ∃ (I : Type), Nonempty I ∧ ∃ (d : I → ℕ) (Φ : (i : I) → MatrixMap (d i)),
      ∀ i, ConjecturedMember (d i) (Φ i) := by
  rintro ⟨I, hI, d, Φ, h⟩
  letI : Nonempty I := hI
  exact no_nonempty_family d Φ h

end Conjecture989
