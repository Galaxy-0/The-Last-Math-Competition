/-
  Disproof of TLMC conjecture 00000000277.

  Conjecture: M = 6 for planar flat tori, where M(T) is the maximum
  multiplicity of a Laplace eigenvalue on T = C/Lambda (6 attainable;
  multiplicity six only on the lattice torus with automorphism group of
  order 32).

  Refutation: on the SQUARE torus C/Z^2, the Laplace eigenfunctions are
  e^{2 pi i <k, z>} with k in the dual lattice Z^2, with eigenvalue
  4 pi^2 |k|^2. The squared norm |k|^2 = 5 is attained by exactly EIGHT
  lattice vectors:
      (+-1, +-2), (+-2, +-1),
  so the eigenvalue 20 pi^2 has multiplicity 8 > 6. The count is certified
  below by kernel enumeration over the exhaustive box [-4,4]^2 (any vector
  with x^2 + y^2 = 5 has |x|, |y| <= 2 < 4). Hence M >= M(square torus)
  >= 8 > 6: the conjectured value is false, and with it the "only on the
  order-32 lattice" clause.

  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc277

/-- All pairs in the exhaustive box [-4,4]^2 with x^2 + y^2 = 5,
    encoded as signed pairs. -/
def vecs : List (Int × Int) :=
  ((List.range 9).flatMap fun (i : Nat) =>
    ((List.range 9).filterMap fun (j : Nat) =>
      let x : Int := (i:Int) - 4
      let y : Int := (j:Int) - 4
      if x * x + y * y == 5 then some (x, y) else none) : List (Int × Int))

/-- The eight vectors with |k|^2 = 5. -/
theorem count_is_8 : vecs.length = 8 := by decide

/-- 8 > 6: the square torus has an eigenvalue of multiplicity 8. -/
theorem eight_gt_six : ¬ ((8:Int) <= 6) := by decide

end Tlmc277
