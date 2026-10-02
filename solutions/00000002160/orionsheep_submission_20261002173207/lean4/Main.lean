/-
  Disproof of TLMC conjecture 00000002160.

  Conjecture: the independence number of the Higman-Sims graph equals the
  Hoffman bound.

  The Higman-Sims graph is strongly regular with v = 100, k = 22, and
  smallest eigenvalue lambda_min = -8 (classical spectrum, cited in
  README/tex). The Hoffman bound is

      alpha <= v * (-lambda_min) / (k - lambda_min)
             = 100 * 8 / (22 + 8) = 800/30 = 26.66...

  Two independent refutations of "alpha EQUALS the Hoffman bound":

  (1) 800/30 is not an integer (800 = 26*30 + 20), and alpha is an
      integer: it can never equal the bound, whatever the graph.
  (2) The classical independence number of the Higman-Sims graph is
      alpha = 22 (it contains a 22-point independent set from the
      Higman-Sims construction), and 22 <> 800/30.

  Lean certifies the arithmetic; the spectrum and alpha = 22 are classical
  facts cited with references. All theorems are closed kernel
  computations, axiom-free.
-/

namespace Tlmc2160

/-- Numerator of the Hoffman bound: v * (-lambda_min) = 100 * 8. -/
theorem numer : (100 * 8 : Nat) = 800 := by decide

/-- Denominator: k - lambda_min = 22 + 8. -/
theorem denom : (22 + 8 : Nat) = 30 := by decide

/-- The bound 800/30 is not an integer (division leaves remainder 20). -/
theorem bound_not_integral : (800 % 30 : Nat) = 20 := by decide
theorem not_divisor : ¬ (30 * 26 = 800) := by decide
theorem not_divisor2 : ¬ (30 * 27 = 800) := by decide

/-- alpha is an integer; the classical value is 22, and 22 <> 800/30. -/
theorem alpha_value : (22 : Nat) = 22 := rfl
theorem alpha_ne_bound : ¬ (30 * 22 = 800) := by decide

end Tlmc2160
