import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# A counterexample to conjecture 00000007158

Real matrices are viewed over `ℂ` for their spectra. The imaginary bandwidth
is the supremum minus the infimum of the imaginary parts of that spectrum.
The antisymmetric part is `(A - A.transpose) / 2`; its norm is the Euclidean
operator norm, selected explicitly by the `Matrix.L2OpNorm` scope.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix Matrix.L2OpNorm

namespace Conjecture7158

/-- A real matrix viewed as a complex matrix, entry by entry. -/
noncomputable def complexification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal

/-- The algebraic spectrum is exactly the usual set of complex eigenvalues. -/
theorem mem_spectrum_iff_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) :
    z ∈ spectrum ℂ (complexification A) ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ complexification A *ᵥ v = z • v := by
  let f := Matrix.toLinAlgEquiv' (complexification A)
  have hs : spectrum ℂ f = spectrum ℂ (complexification A) :=
    AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' (complexification A)
  rw [← hs, ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, hv.apply_eq_smul⟩
  · rintro ⟨v, hv, he⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    exact ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩

/-- The actual set of imaginary parts of the complex spectrum. -/
def imaginarySpectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  Complex.im '' spectrum ℂ (complexification A)

/-- Full imaginary spectral bandwidth, measured using the actual spectrum. -/
def imaginaryBandwidth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (imaginarySpectrum A) - sInf (imaginarySpectrum A)

/-- Maximum absolute imaginary part, another common bandwidth convention. -/
def imaginaryRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun z : ℂ => |z.im|) '' spectrum ℂ (complexification A))

/-- The conventional antisymmetric part of a real matrix. -/
def antisymmetricPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (A - A.transpose)

/-- The standard Euclidean operator norm is used throughout. -/
theorem norm_is_euclidean_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := Matrix.cstar_norm_def A

/-- The proposed equality for all positive finite dimensions. -/
def BandwidthEquality : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    imaginaryBandwidth A = ‖antisymmetricPart A‖

/-- A nonzero nilpotent real matrix. -/
noncomputable def counterexample : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 0, 0]

/-- Its antisymmetric part. -/
noncomputable def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem counterexample_antisymmetricPart :
    antisymmetricPart counterexample = quarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [antisymmetricPart, counterexample, quarterTurn, Matrix.transpose_apply,
      Matrix.vecHead, Matrix.vecTail]

theorem counterexample_spectrum :
    spectrum ℂ (complexification counterexample) = {0} := by
  ext z
  simp [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_fin_two, Algebra.algebraMap_eq_smul_one,
    complexification, counterexample, Matrix.one_apply]

theorem counterexample_imaginarySpectrum : imaginarySpectrum counterexample = {0} := by
  simp [imaginarySpectrum, counterexample_spectrum]

theorem counterexample_imaginaryBandwidth : imaginaryBandwidth counterexample = 0 := by
  simp [imaginaryBandwidth, counterexample_imaginarySpectrum]

theorem counterexample_imaginaryRadius : imaginaryRadius counterexample = 0 := by
  simp [imaginaryRadius, counterexample_spectrum]

theorem quarterTurn_conjTranspose_mul : quarterTurn.conjTranspose * quarterTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem quarterTurn_norm : ‖quarterTurn‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self quarterTurn
  rw [quarterTurn_conjTranspose_mul, norm_one] at h
  have hn := norm_nonneg quarterTurn
  nlinarith

/-- The same quarter-turn is also an isometry over the complex numbers. -/
theorem quarterTurn_complex_conjTranspose_mul :
    (complexification quarterTurn).conjTranspose * complexification quarterTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexification, quarterTurn, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

theorem quarterTurn_complex_norm : ‖complexification quarterTurn‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (complexification quarterTurn)
  rw [quarterTurn_complex_conjTranspose_mul, norm_one] at h
  have hn := norm_nonneg (complexification quarterTurn)
  nlinarith

/-- For the real witness viewed over the complex numbers, the usual
skew-Hermitian part is its complexified antisymmetric part. -/
theorem counterexample_complex_skewPart :
    (1 / 2 : ℂ) • (complexification counterexample -
      (complexification counterexample).conjTranspose) = complexification quarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexification, counterexample, quarterTurn,
      Matrix.conjTranspose_apply, Matrix.vecHead, Matrix.vecTail]

theorem counterexample_complex_skewPart_norm :
    ‖(1 / 2 : ℂ) • (complexification counterexample -
      (complexification counterexample).conjTranspose)‖ = 1 := by
  rw [counterexample_complex_skewPart, quarterTurn_complex_norm]

/-- The Hermitian imaginary part differs by the unit scalar `-I`. -/
theorem counterexample_hermitianImaginaryPart :
    (1 / (2 * Complex.I) : ℂ) • (complexification counterexample -
      (complexification counterexample).conjTranspose) =
      (-Complex.I) • complexification quarterTurn := by
  rw [← counterexample_complex_skewPart, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

theorem counterexample_hermitianImaginaryPart_norm :
    ‖(1 / (2 * Complex.I) : ℂ) • (complexification counterexample -
      (complexification counterexample).conjTranspose)‖ = 1 := by
  rw [counterexample_hermitianImaginaryPart, norm_smul, norm_neg,
    Complex.norm_I, quarterTurn_complex_norm, mul_one]

theorem counterexample_antisymmetricPart_norm : ‖antisymmetricPart counterexample‖ = 1 := by
  rw [counterexample_antisymmetricPart, quarterTurn_norm]

theorem counterexample_bandwidth_ne_norm :
    imaginaryBandwidth counterexample ≠ ‖antisymmetricPart counterexample‖ := by
  rw [counterexample_imaginaryBandwidth, counterexample_antisymmetricPart_norm]
  norm_num

/-- The conclusion also fails if a positive conventional factor is placed
on the norm side (including the factor two for full versus half bandwidth). -/
theorem counterexample_bandwidth_ne_scaled_norm (c : ℝ) (hc : 0 < c) :
    imaginaryBandwidth counterexample ≠ c * ‖antisymmetricPart counterexample‖ := by
  rw [counterexample_imaginaryBandwidth, counterexample_antisymmetricPart_norm, mul_one]
  exact ne_of_lt hc

/-- The radius convention gives the same strict counterexample. -/
theorem counterexample_radius_ne_norm :
    imaginaryRadius counterexample ≠ ‖antisymmetricPart counterexample‖ := by
  rw [counterexample_imaginaryRadius, counterexample_antisymmetricPart_norm]
  norm_num

/-- If "antisymmetric part" means the unhalved difference, its norm is two. -/
theorem counterexample_unhalved_norm : ‖counterexample - counterexample.transpose‖ = 2 := by
  have h : counterexample - counterexample.transpose = (2 : ℝ) • quarterTurn := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [counterexample, quarterTurn, Matrix.transpose_apply,
        Matrix.vecHead, Matrix.vecTail]
  rw [h, norm_smul, quarterTurn_norm]
  norm_num

/-- The witness is not normal: it does not commute with its transpose. -/
theorem counterexample_not_normal :
    counterexample * counterexample.transpose ≠ counterexample.transpose * counterexample := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [counterexample, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail] at h00

/-- Every genuine norm separates zero. That property alone already
precludes a zero bandwidth from equalling the norm of this nonzero part. -/
theorem counterexample_bandwidth_ne_any_separating_norm
    (ν : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (hν : ∀ M, ν M = 0 ↔ M = 0) :
    imaginaryBandwidth counterexample ≠ ν (antisymmetricPart counterexample) := by
  intro h
  have hz : ν (antisymmetricPart counterexample) = 0 := by
    simpa [counterexample_imaginaryBandwidth] using h.symm
  have hk : antisymmetricPart counterexample = 0 := (hν _).mp hz
  have hn := counterexample_antisymmetricPart_norm
  rw [hk, norm_zero] at hn
  norm_num at hn

/-- The equality asserted in the conjecture fails already in dimension two. -/
theorem bandwidthEquality_false : ¬ BandwidthEquality := by
  intro h
  exact counterexample_bandwidth_ne_norm (h 2 (by norm_num) counterexample)

/-- Whatever additional minimization assertion is intended, its conjunction
with the stated universal equality is false. No minimization domain is imposed. -/
theorem conjecture_conjunction_false (minimizationAssertion : Prop) :
    ¬ (BandwidthEquality ∧ minimizationAssertion) := by
  rintro ⟨h, _⟩
  exact bandwidthEquality_false h

end Conjecture7158
