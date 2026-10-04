import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

namespace Conjecture978

/-- The nilpotent two-dimensional matrix used throughout the counterexample. -/
def witness : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

/-- The real Hermitian part of a complex matrix. -/
def hermitianPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + A.conjTranspose)

/-- The imaginary Hermitian part of a complex matrix. -/
def imaginaryPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (1 / (2 * Complex.I) : ℂ) • (A - A.conjTranspose)

theorem hermitianPart_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (hermitianPart A).IsHermitian := by
  ext i j
  simp [hermitianPart, Matrix.conjTranspose_apply, star_add, star_div]
  ring

theorem imaginaryPart_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (imaginaryPart A).IsHermitian := by
  ext i j
  simp [imaginaryPart, Matrix.conjTranspose_apply, star_sub, star_div, Complex.inv_I]
  ring

/-- The homogeneous determinant pencil, with coordinates `(u,v,w)`. -/
def pencilPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  Matrix.det (fun i j => C (hermitianPart A i j) * X 0 +
    C (imaginaryPart A i j) * X 1 + if i = j then X 2 else 0)

/-- Polynomial evaluation is the determinant of the actual Hermitian matrix pencil. -/
theorem eval_pencilPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q : Fin 3 → ℂ) :
    eval q (pencilPolynomial A) =
      (q 0 • hermitianPart A + q 1 • imaginaryPart A + q 2 • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
  unfold pencilPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply, mul_comm]

theorem hermitianPart_witness : hermitianPart witness = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hermitianPart, witness, Matrix.conjTranspose_apply]

theorem imaginaryPart_witness : imaginaryPart witness = !![0, -Complex.I; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [imaginaryPart, witness, Matrix.conjTranspose_apply, Complex.inv_I] <;> ring

/-- The exact determinant polynomial, derived from the matrix entries. -/
theorem pencilPolynomial_witness : pencilPolynomial witness =
    (X 2 : MvPolynomial (Fin 3) ℂ)^2 - X 0^2 - X 1^2 := by
  simp [pencilPolynomial, hermitianPart_witness, imaginaryPart_witness, Matrix.det_fin_two]
  ring_nf
  simp [← map_pow, Complex.I_sq]
  ring

/-- The evaluated formal gradient of a ternary polynomial. -/
def gradient (p : MvPolynomial (Fin 3) ℂ) (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun j => eval q (pderiv j p)

/-- Every nonzero point of the affine cone over the projective curve is nonsingular. -/
def ProjectivelySmooth (p : MvPolynomial (Fin 3) ℂ) : Prop :=
  ∀ q : Fin 3 → ℂ, q ≠ 0 → eval q p = 0 → gradient p q ≠ 0

theorem gradient_witness (q : Fin 3 → ℂ) :
    gradient (pencilPolynomial witness) q = ![-2 * q 0, -2 * q 1, 2 * q 2] := by
  ext j
  fin_cases j <;> simp [gradient, pencilPolynomial_witness, pderiv_pow]

theorem pencilPolynomial_witness_smooth : ProjectivelySmooth (pencilPolynomial witness) := by
  intro q hq _ hg
  apply hq
  rw [gradient_witness] at hg
  funext j
  fin_cases j
  · change q 0 = 0
    have h : -2 * q 0 = 0 := congrFun hg 0
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · change q 1 = 0
    have h : -2 * q 1 = 0 := congrFun hg 1
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · change q 2 = 0
    have h : 2 * q 2 = 0 := congrFun hg 2
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem pencilPolynomial_witness_homogeneous :
    (pencilPolynomial witness).IsHomogeneous 2 := by
  rw [pencilPolynomial_witness]
  exact ((isHomogeneous_X_pow (2 : Fin 3) 2).sub (isHomogeneous_X_pow 0 2)).sub
    (isHomogeneous_X_pow 1 2)

theorem pencilPolynomial_witness_ne_zero : pencilPolynomial witness ≠ 0 := by
  intro h
  have he := congrArg (eval ![(0 : ℂ), 0, 1]) h
  norm_num [pencilPolynomial_witness] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

theorem pencilPolynomial_witness_totalDegree : (pencilPolynomial witness).totalDegree = 2 :=
  pencilPolynomial_witness_homogeneous.totalDegree pencilPolynomial_witness_ne_zero

theorem witness_sq_zero : witness ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pow_two, witness, Matrix.mul_apply, Fin.sum_univ_two]

theorem charpoly_witness : witness.charpoly = Polynomial.X ^ 2 := by
  simp [Matrix.charpoly, Matrix.det_fin_two, witness, pow_two]

end Conjecture978
