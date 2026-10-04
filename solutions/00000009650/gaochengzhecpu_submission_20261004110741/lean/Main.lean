import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Distinct real eigenvalues of a symmetric operator have zero cross-overlap. -/

namespace Conjecture9650

open Filter Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem distinct_eigenvectors_inner_zero (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (u v : E) (a b : ℝ) (hu : T u = a • u) (hv : T v = b • v) (hab : a ≠ b) :
    @inner ℝ E _ u v = 0 := by
  have h : a * @inner ℝ E _ u v = b * @inner ℝ E _ u v := by
    simpa only [hu, hv, real_inner_smul_left, real_inner_smul_right] using hT u v
  by_contra hz
  exact hab (mul_right_cancel₀ hz h)

def upperPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

theorem upperPairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (upperPairs n).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [upperPairs]

noncomputable def overlap {n : ℕ} (u : Fin n → E) (i j : Fin n) : ℝ :=
  (@inner ℝ E _ (u i) (u j)) ^ 2

/-- The empirical average of a test function over distinct-index upper entries. -/
noncomputable def empiricalAverage {n : ℕ} (u : Fin n → E) (f : ℝ → ℝ) : ℝ :=
  (∑ ij ∈ upperPairs n, f (overlap u ij.1 ij.2)) / (upperPairs n).card

noncomputable def overlapMean {n : ℕ} (u : Fin n → E) : ℝ :=
  empiricalAverage u id

theorem all_cross_overlaps_zero {n : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (u : Fin n → E) (e : Fin n → ℝ) (he : Function.Injective e)
    (hu : ∀ i, T (u i) = e i • u i) {i j : Fin n} (hij : i ≠ j) :
    overlap u i j = 0 := by
  unfold overlap
  rw [distinct_eigenvectors_inner_zero T hT (u i) (u j) (e i) (e j)
    (hu i) (hu j) (fun h => hij (he h))]
  norm_num

theorem empirical_point_mass {n : ℕ} (hn : 2 ≤ n) (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (u : Fin n → E) (e : Fin n → ℝ)
    (he : Function.Injective e) (hu : ∀ i, T (u i) = e i • u i) (f : ℝ → ℝ) :
    empiricalAverage u f = f 0 := by
  have hzero : ∀ ij ∈ upperPairs n, overlap u ij.1 ij.2 = 0 := by
    intro ij hij
    have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    exact all_cross_overlaps_zero T hT u e he hu (ne_of_lt hlt)
  unfold empiricalAverage
  simp_rw [Finset.sum_congr rfl (fun ij hij => congrArg f (hzero ij hij))]
  have hc : ((upperPairs n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (upperPairs_nonempty hn)).ne'
  simp [hc, nsmul_eq_mul, mul_div_cancel_left₀]

theorem mean_zero {n : ℕ} (hn : 2 ≤ n) (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (u : Fin n → E) (e : Fin n → ℝ) (he : Function.Injective e)
    (hu : ∀ i, T (u i) = e i • u i) : overlapMean u = 0 :=
  empirical_point_mass hn T hT u e he hu id

theorem mean_not_two_div_n {n : ℕ} (hn : 2 ≤ n) (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (u : Fin n → E) (e : Fin n → ℝ)
    (he : Function.Injective e) (hu : ∀ i, T (u i) = e i • u i) :
    overlapMean u ≠ 2 / (n : ℝ) := by
  rw [mean_zero hn T hT u e he hu]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_pos (by norm_num : (0 : ℝ) < 2) hn0).ne

/-- A concrete family of symmetric matrices of every finite order. -/
noncomputable def diagonalOperator (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.diagonal (fun i : Fin n => (i.val : ℝ))).toEuclideanLin

noncomputable def basisVector (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

theorem diagonal_symmetric (n : ℕ) : (diagonalOperator n).IsSymmetric := by
  exact Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_diagonal _)

theorem basisVector_normalized (n : ℕ) (i : Fin n) : ‖basisVector n i‖ = 1 := by
  simp [basisVector]

theorem distinct_diagonal_eigenvalues (n : ℕ) :
    Function.Injective (fun i : Fin n => (i.val : ℝ)) := by
  intro i j h
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at h
  exact_mod_cast h

theorem basisVector_eigenvector (n : ℕ) (i : Fin n) :
    diagonalOperator n (basisVector n i) = (i.val : ℝ) • basisVector n i := by
  ext j
  by_cases h : i = j
  · subst j
    simp [diagonalOperator, basisVector, Matrix.toEuclideanLin_apply,
      Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, Matrix.diagonal_apply]
  · simp [diagonalOperator, basisVector, Matrix.toEuclideanLin_apply,
      Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, Matrix.diagonal_apply, h, Ne.symm h]

/-- Every member of this type contains actual normalized eigenvectors of an actual operator. -/
structure SymmetricSystem (n : ℕ) where
  operator : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
  symmetric : operator.IsSymmetric
  vectors : Fin n → EuclideanSpace ℝ (Fin n)
  values : Fin n → ℝ
  distinct : Function.Injective values
  eigenvector : ∀ i, operator (vectors i) = values i • vectors i
  normalized : ∀ i, ‖vectors i‖ = 1

theorem any_symmetric_scaled_limit_zero (s : ∀ n, SymmetricSystem (n + 2)) :
    Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * overlapMean (s n).vectors)
      atTop (𝓝 0) := by
  have hz : ∀ n, overlapMean (s n).vectors = 0 := fun n =>
    mean_zero (by omega) (s n).operator (s n).symmetric (s n).vectors
      (s n).values (s n).distinct (s n).eigenvector
  simp only [hz, mul_zero]
  exact tendsto_const_nhds

theorem any_symmetric_not_claimed_scaled_limit (s : ∀ n, SymmetricSystem (n + 2)) :
    ¬ Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * overlapMean (s n).vectors)
      atTop (𝓝 2) := by
  intro h
  have h02 : (0 : ℝ) = 2 := tendsto_nhds_unique (any_symmetric_scaled_limit_zero s) h
  norm_num at h02

theorem concrete_mean_zero (n : ℕ) : overlapMean (basisVector (n + 2)) = 0 :=
  mean_zero (by omega) (diagonalOperator (n + 2)) (diagonal_symmetric (n + 2))
    (basisVector (n + 2)) (fun i => (i.val : ℝ)) (distinct_diagonal_eigenvalues (n + 2))
    (basisVector_eigenvector (n + 2))

theorem concrete_counterexample (n : ℕ) :
    (diagonalOperator (n + 2)).IsSymmetric ∧
    (∀ i, ‖basisVector (n + 2) i‖ = 1) ∧
    (∀ i, diagonalOperator (n + 2) (basisVector (n + 2) i) =
      (i.val : ℝ) • basisVector (n + 2) i) ∧
    overlapMean (basisVector (n + 2)) ≠ 2 / ((n + 2 : ℕ) : ℝ) := by
  exact ⟨diagonal_symmetric _, basisVector_normalized _, basisVector_eigenvector _,
    mean_not_two_div_n (by omega) _ (diagonal_symmetric _) _ _
      (distinct_diagonal_eigenvalues _) (basisVector_eigenvector _)⟩

theorem scaled_mean_limit_zero :
    Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * overlapMean (basisVector (n + 2)))
      atTop (𝓝 0) := by
  simp only [concrete_mean_zero, mul_zero]
  exact tendsto_const_nhds

theorem not_claimed_scaled_limit :
    ¬ Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * overlapMean (basisVector (n + 2)))
      atTop (𝓝 2) := by
  intro h
  have h02 : (0 : ℝ) = 2 := tendsto_nhds_unique scaled_mean_limit_zero h
  norm_num at h02

#print axioms distinct_eigenvectors_inner_zero
#print axioms empirical_point_mass
#print axioms mean_not_two_div_n
#print axioms concrete_counterexample
#print axioms any_symmetric_not_claimed_scaled_limit
#print axioms scaled_mean_limit_zero
#print axioms not_claimed_scaled_limit

end Conjecture9650
