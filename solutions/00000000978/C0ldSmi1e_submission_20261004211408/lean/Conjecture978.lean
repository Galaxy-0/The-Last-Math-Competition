import Conjecture978.Boundary

noncomputable section

namespace Conjecture978

/-- A necessary specialization of the proposed real-point bound: even two-dimensional
matrices with a smooth degree-two determinant curve must satisfy the claimed bound.
The curve here is the real algebraic boundary of the actual numerical range, as in the source. -/
def RealPointBoundClaim : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
    (pencilPolynomial A).IsHomogeneous 2 → ProjectivelySmooth (pencilPolynomial A) →
      (algebraicBoundary A).encard ≤ (2 * (2 - 1) / 2 : ℕ)

/-- The same necessary specialization using the ordinary projective dual of a smooth pencil.
No equivalence with the algebraic boundary is asserted for arbitrary matrices. -/
def DualPointBoundClaim : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
    (pencilPolynomial A).IsHomogeneous 2 → ProjectivelySmooth (pencilPolynomial A) →
      (realAffinePoints (pencilPolynomial A)).encard ≤ (2 * (2 - 1) / 2 : ℕ)

/-- The source's bound already fails on the explicit smooth two-dimensional example. -/
theorem conjecture978_disproof : ¬ RealPointBoundClaim := by
  intro h
  exact algebraicBoundary_witness_no_finite_bound _
    (h witness pencilPolynomial_witness_homogeneous pencilPolynomial_witness_smooth)

/-- The same example also refutes the bound under the standard projective-dual convention. -/
theorem dualPointBoundClaim_false : ¬ DualPointBoundClaim := by
  intro h
  exact realAffinePoints_witness_no_finite_bound _
    (h witness pencilPolynomial_witness_homogeneous pencilPolynomial_witness_smooth)

/-- Consequently the unrestricted bound over all matrix dimensions is false as well. -/
theorem universal_algebraicBoundary_bound_false :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      (algebraicBoundary A).encard ≤ (n * (n - 1) / 2 : ℕ)) := by
  intro h
  exact algebraicBoundary_witness_no_finite_bound _ (h 2 witness)

/-- A concrete certificate tying together the matrix, its multiplicity polynomial,
its smooth determinant pencil, and the two actual infinite real curves. -/
theorem witness_certificate :
    witness.charpoly = Polynomial.X ^ 2 ∧
    (pencilPolynomial witness).IsHomogeneous 2 ∧
    ProjectivelySmooth (pencilPolynomial witness) ∧
    (algebraicBoundary witness).Infinite ∧
    realAffinePoints (pencilPolynomial witness) = algebraicBoundary witness :=
  ⟨charpoly_witness, pencilPolynomial_witness_homogeneous,
    pencilPolynomial_witness_smooth, algebraicBoundary_witness_infinite,
    realAffinePoints_eq_algebraicBoundary_witness⟩

end Conjecture978
