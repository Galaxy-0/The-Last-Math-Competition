/-
  Disproof of TLMC conjecture 00000002142.

  Conjecture: the number of cospectral mates with SRG parameters
  (460, 153, 32, 57) is explicit, and the kernel of that number is a
  biplane count.

  Every strongly regular graph with parameters (v, k, lambda, mu)
  satisfies the classical two-path counting identity

      k * (k - lambda - 1) = (v - k - 1) * mu

  (from a fixed vertex x, count length-2 paths to vertices non-adjacent
  to x: each of the k neighbors of x has k - lambda - 1 further
  neighbors, and each of the v - k - 1 non-neighbors of x is reached
  exactly mu times). For (460, 153, 32, 57):

      153 * (153 - 32 - 1) = 153 * 120 = 18360
      (460 - 153 - 1) * 57 = 306 * 57    = 17442

  and 18360 <> 17442. Hence NO strongly regular graph with parameters
  (460, 153, 32, 57) exists, and the conjectured "explicit number of
  cospectral mates" (with its biplane kernel) has no subject matter.

  The necessity of the identity is classical SRG theory (counting proof
  restated in README/tex); the Lean certificate checks the arithmetic
  violation in closed form. All theorems are closed kernel
  computations, axiom-free.
-/

namespace Tlmc2142

/-- k - lambda - 1 = 153 - 32 - 1 = 120. -/
theorem kle : (153 - 32 - 1 : Nat) = 120 := by decide

/-- v - k - 1 = 460 - 153 - 1 = 306. -/
theorem vkm : (460 - 153 - 1 : Nat) = 306 := by decide

/-- Left side: 153 * 120 = 18360. -/
theorem lhs : (153 * 120 : Nat) = 18360 := by decide

/-- Right side: 306 * 57 = 17442. -/
theorem rhs : (306 * 57 : Nat) = 17442 := by decide

/-- The two-path identity FAILS at (460, 153, 32, 57): no SRG with these
    parameters exists, so there are no cospectral mates to count. -/
theorem identity_fails : ¬ (18360 = 17442) := by decide

end Tlmc2142
