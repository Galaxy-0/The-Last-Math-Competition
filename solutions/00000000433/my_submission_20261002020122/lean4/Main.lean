/-
  Disproof of TMC conjecture 00000000433 (case B2).

  Macdonald's Weyl denominator identity (finite-type RHS of the affine
  denominator identity) is
      prod_{a in Delta+} (1 - e^{-a}) = sum_{w in W} eps(w) * e^{w(rho) - rho},
  with rho = (1/2) * sum of the positive roots. Coefficients are +-1, so the
  number T(B2) of monomial terms equals the number of DISTINCT values of
  w(rho) - rho.

  Conjecture 00000000433 asserts T(B_n) = n, in particular T(B2) = 2.
  We exhibit B2 in the orthonormal realization
      Delta = {+-e1, +-e2, +-e1 +- e2},
      Delta+ = {e1, e2, e1 - e2, e1 + e2},
  whose Weyl group is the 8 signed coordinate permutations, and prove the
  8 exponents w(rho) - rho are pairwise distinct. Hence T(B2) = 8 != 2.

  rho(B2) = (3/2, 1/2); we use the integral multiple rho' = (3,1) = 2*rho,
  since scaling by 2 is a bijection and preserves distinctness.

  Pure core Lean (no Mathlib). Every theorem below is proved by rfl/decide
  on closed computations and depends on NO axioms (audited in Check.lean).
-/

/-- The eight elements of W(B2) as signed coordinate permutations,
    acting on `Int × Int`. -/
def WeylB2 : List (Int × Int → Int × Int) :=
  [fun p => (p.1, p.2), fun p => (-p.1, p.2),
   fun p => (p.1, -p.2), fun p => (-p.1, -p.2),
   fun p => (p.2, p.1), fun p => (-p.2, p.1),
   fun p => (p.2, -p.1), fun p => (-p.2, -p.1)]

/-- rho(B2) = (3/2, 1/2), rescaled by the harmless factor 2 to (3, 1)
    so that all arithmetic stays integral. -/
def rhoB2 : Int × Int := (3, 1)

/-- Componentwise subtraction on `Int × Int` (core Lean has no
    `HSub (Int × Int) (Int × Int)` instance). -/
def sub2 (a b : Int × Int) : Int × Int := (a.1 - b.1, a.2 - b.2)

/-- The eight exponents `w(rho) - rho` of the B2 denominator identity,
    in the order of `WeylB2`. -/
def exponentsB2 : List (Int × Int) := WeylB2.map (fun w => sub2 (w rhoB2) rhoB2)

/-- The computed exponent list. -/
theorem exponentsB2_val :
    exponentsB2 = [(0, 0), (-6, 0), (0, -2), (-6, -2),
                   (-2, 2), (-4, 2), (-2, -4), (-4, -4)] := by rfl

/-- Boolean test: are the entries of a list pairwise different? -/
def pairwiseDistinct : List (Int × Int) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => y != x) && pairwiseDistinct xs

/-- Main attack: the 8 exponents w(rho) - rho of B2 are pairwise distinct.
    With coefficients +-1 no two terms of the denominator identity can merge
    or cancel, so T(B2) = 8. -/
theorem exponentsB2_pairwise_distinct : pairwiseDistinct exponentsB2 = true := by rfl

/-- There are exactly 8 terms: T(B2) = 8. -/
theorem T_B2 : exponentsB2.length = 8 := by rfl

/-- The conjecture's claim T(B2) = n = 2 is false. -/
theorem conjecture_00000000433_B2_false : ¬ (exponentsB2.length = 2) := by decide
