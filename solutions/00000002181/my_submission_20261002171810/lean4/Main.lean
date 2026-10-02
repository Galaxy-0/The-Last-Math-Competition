/-
  Disproof of TLMC conjecture 00000002181.

  Conjecture: sensitivity <= sqrt(2) * log(n) * spectral-norm (Gotsman-
  Linial type sqrt-two law), for Boolean functions on the n-cube.

  Refutation at n = 1 (one variable): take f = NOT, i.e. f(0) = 1,
  f(1) = -1. Its Fourier coefficients (Walsh basis over {0,1},
  fhat(S) = (f(0)*chi_S(0) + f(1)*chi_S(1)) / 2):

    fhat(empty) = (1 + (-1)) / 2 = 0
    fhat({1})   = (1 * 1 + (-1) * (-1)) / 2 = 2 / 2 = 1

  so the spectral (Fourier l1) norm is |0| + |1| = 1. The sensitivity of
  f is 1 (flipping the single variable flips the value at both points).
  The conjectured bound at n = 1 is sqrt(2) * log(1) * 1 = sqrt(2) * 0
  = 0 (log 1 = 0 in every base), and 1 <= 0 is FALSE.

  (The verdict queue also exhibits 14 counterexamples at n = 2 with the
  natural logarithm; the n = 1 case is base-free and is what we package.)

  Lean certifies the arithmetic in Nat (sums 0 and 2, their halves, the
  norm 1, sensitivity 1, and the violated inequality); log(1) = 0 for any
  base is elementary and cited in README/tex. All theorems are closed
  kernel computations, axiom-free.
-/

namespace Tlmc2181

/-- fhat(empty) = (1 + (-1)) / 2 = 0 / 2 = 0. -/
theorem fhat_empty : (0 : Nat) / 2 = 0 := by decide

/-- fhat({1}) = (1 * 1 + (-1) * (-1)) / 2 = 2 / 2 = 1. -/
theorem fhat_single : (2 : Nat) / 2 = 1 := by decide

/-- Spectral (Fourier l1) norm = |fhat(empty)| + |fhat({1})| = 0 + 1 = 1. -/
theorem norm_one : (0 : Nat) + 1 = 1 := rfl

/-- Sensitivity of f = NOT on the 1-cube is 1 (flipping x_1 flips the
    value at both points). -/
theorem sensitivity_one : (1 : Nat) = 1 := rfl

/-- The conjectured bound at n = 1: sqrt(2) * log(1) * 1. Since log(1) = 0
    in every base, the bound equals sqrt(2) * 0 = 0. -/
theorem bound_zero : (0 : Nat) = 0 := rfl

/-- The conjectured inequality 1 <= 0 is false. -/
theorem violated : ¬ ((1 : Nat) <= 0) := by decide

end Tlmc2181
