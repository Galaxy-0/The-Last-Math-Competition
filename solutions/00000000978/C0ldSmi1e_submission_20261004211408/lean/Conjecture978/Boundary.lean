import Conjecture978.DualCurve
import Conjecture978.NumericalRange
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Card

noncomputable section
open scoped BigOperators

namespace Conjecture978

/-- Real affine coordinates in the complex plane. -/
def realCoordinatePoint (x : Fin 2 → ℝ) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

/-- The real unit circle. -/
def circle : Set (Fin 2 → ℝ) := {x | (x 0)^2 + (x 1)^2 = 1}

/-- A polynomial defining the circle in the real affine plane. -/
def circlePolynomial : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1

theorem circle_eq_zeroLocus :
    circle = MvPolynomial.zeroLocus (Ideal.span {circlePolynomial}) := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp [circle, circlePolynomial, sub_eq_zero]

theorem algebraicClosure_circle : algebraicClosure circle = circle := by
  rw [circle_eq_zeroLocus, algebraicClosure_zeroLocus]

theorem realCoordinatePoint_mem_sphere (x : Fin 2 → ℝ) :
    realCoordinatePoint x ∈ Metric.sphere (0 : ℂ) 1 ↔ x ∈ circle := by
  rw [mem_sphere_zero_iff_norm]
  have hn := norm_nonneg (realCoordinatePoint x)
  have hs : ‖realCoordinatePoint x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_add_mul_I _ _
  change ‖realCoordinatePoint x‖ = 1 ↔ (x 0)^2 + (x 1)^2 = 1
  constructor <;> intro h <;> nlinarith

/-- Rational stereographic parametrization of all but one point of the circle. -/
def circleParam (t : ℝ) : Fin 2 → ℝ :=
  ![(1 - t^2) / (1 + t^2), 2*t / (1 + t^2)]

theorem circleParam_mem (t : ℝ) : circleParam t ∈ circle := by
  change ((1-t^2)/(1+t^2))^2 + (2*t/(1+t^2))^2 = 1
  have hd : 1 + t^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem circleParam_inverse (t : ℝ) :
    circleParam t 1 / (1 + circleParam t 0) = t := by
  have hd : 1 + t^2 ≠ 0 := ne_of_gt (by positivity)
  have he : 1 + (1-t^2)/(1+t^2) = 2/(1+t^2) := by
    field_simp
    ring
  change (2*t/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) = t
  rw [he]
  field_simp

theorem circleParam_injective : Function.Injective circleParam := by
  intro t u h
  calc
    t = circleParam t 1 / (1 + circleParam t 0) := (circleParam_inverse t).symm
    _ = circleParam u 1 / (1 + circleParam u 0) := congrArg (fun x => x 1 / (1+x 0)) h
    _ = u := circleParam_inverse u

theorem circle_infinite : circle.Infinite := by
  apply (Set.infinite_range_of_injective circleParam_injective).mono
  rintro x ⟨t, rfl⟩
  exact circleParam_mem t

theorem circle_encard : circle.encard = ⊤ := circle_infinite.encard_eq

theorem realAffinePoints_witness_eq_circle :
    realAffinePoints (pencilPolynomial witness) = circle := realAffinePoints_witness_eq

theorem realAffinePoints_witness_infinite :
    (realAffinePoints (pencilPolynomial witness)).Infinite := by
  rw [realAffinePoints_witness_eq_circle]
  exact circle_infinite

theorem realAffinePoints_witness_encard :
    (realAffinePoints (pencilPolynomial witness)).encard = ⊤ :=
  realAffinePoints_witness_infinite.encard_eq

theorem realAffinePoints_witness_no_finite_bound (N : ℕ) :
    ¬ (realAffinePoints (pencilPolynomial witness)).encard ≤ N := by
  rw [realAffinePoints_witness_encard]
  simp

/-- The real Zariski closure of the Euclidean boundary of the actual numerical range. -/
def algebraicBoundary {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set (Fin 2 → ℝ) :=
  algebraicClosure {x | realCoordinatePoint x ∈ frontier (numericalRange A)}

theorem algebraicBoundary_witness_eq_circle : algebraicBoundary witness = circle := by
  unfold algebraicBoundary
  rw [frontier_numericalRange_witness]
  have h : {x : Fin 2 → ℝ | realCoordinatePoint x ∈ Metric.sphere (0 : ℂ) 1} = circle := by
    ext x
    exact realCoordinatePoint_mem_sphere x
  rw [h, algebraicClosure_circle]

/-- For this smooth determinant conic, both constructions give exactly the same real curve. -/
theorem realAffinePoints_eq_algebraicBoundary_witness :
    realAffinePoints (pencilPolynomial witness) = algebraicBoundary witness := by
  rw [realAffinePoints_witness_eq_circle, algebraicBoundary_witness_eq_circle]

theorem algebraicBoundary_witness_infinite : (algebraicBoundary witness).Infinite := by
  rw [algebraicBoundary_witness_eq_circle]
  exact circle_infinite

theorem algebraicBoundary_witness_encard : (algebraicBoundary witness).encard = ⊤ :=
  algebraicBoundary_witness_infinite.encard_eq

theorem algebraicBoundary_witness_no_finite_bound (N : ℕ) :
    ¬ (algebraicBoundary witness).encard ≤ N := by
  rw [algebraicBoundary_witness_encard]
  simp

end Conjecture978
