# Adversarial self-review: conjecture 00000002226

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed and reviewed by a single AI agent. No
independent or external review is claimed.

1. Definition. The source describes the McCoy property as: coefficients
   of zero-divisor polynomials are annihilated. For a possibly
   noncommutative ring the standard form (Nielsen 2006) has a right and
   a left version. The Lean file defines both and their conjunction. The
   result is proved for all three, so no choice of handedness or of
   "McCoy = both sides" versus "McCoy = one side" affects the conclusion.
2. Polynomial ring. Mathlib's A[X] over a noncommutative ring has a
   central indeterminate, which is the polynomial ring used in the
   McCoy literature. The matrix ring is Mathlib's Matrix (Fin n) (Fin n) R
   with its usual ring structure.
3. n = 1. Commutative rings are McCoy by Mathlib's theorem
   Polynomial.nmem_nonZeroDivisors_iff. For the right-handed version the
   product is first commuted, which is legitimate only because R is
   commutative; the lemma is stated for CommRing. The paper contains a
   complete classical proof, which was rechecked line by line: the
   minimal-degree choice, the top coefficient a_l b_m = 0, and the
   contradiction all hold.
4. Transfer. M_1(R) and R are identified by an explicit ring isomorphism
   whose multiplicativity is proved from the matrix product formula. The
   transfer lemmas use injectivity of Polynomial.map along an
   isomorphism; nonvanishing and the nonzero annihilator are carried
   across in both directions.
5. n >= 2, right side. f = (I - E22) + E12 x and g = E21 - E11 x. Hand
   check of the three coefficients of f g: (I - E22)E21 = 0;
   E12E21 - (I - E22)E11 = E11 - E11 = 0; E12E11 = 0. Viewed in M_2(R[x]),
   f is the matrix with rows (1, x) and (0, 0); its kernel is spanned by
   (-x, 1) and contains no nonzero constant vector, which agrees with the
   algebraic argument r = E22 r = E21 E12 r = 0.
6. n >= 2, left side. The mirrored pair f' = E12 - E11 x and
   g' = (I - E22) + E21 x was checked by hand in the same way, including
   E11 E22 = 0 and E11 E21 = 0. The argument s = s E22 = s E21 E12 = 0
   uses s(I - E22) = 0 and s E21 = 0, both read off from C s * g' = 0.
7. Nonvanishing. f, g, f', g' are proved nonzero in Lean from a
   coefficient that is a matrix unit, and matrix units are nonzero
   because the ring is nontrivial. This is where Nontrivial is used.
8. Generality. The counterexample is proved for any finite index type
   with two distinct indices and any nontrivial ring, then specialised to
   Fin n with 2 <= n. Nothing is checked only for n = 2.
9. Main statement. matrix_mcCoy_iff: for CommRing R, Nontrivial R and
   1 <= n, McCoy (Matrix (Fin n) (Fin n) R) <-> n = 1. The forward
   direction uses n != 1 and 1 <= n to get 2 <= n. The one-sided
   equivalences are separate theorems.
10. Scope. The only hypotheses beyond the source text are R != 0 and
    n >= 1. They are necessary: mcCoy_of_subsingleton shows a zero ring
    is McCoy vacuously, so for R = 0 or n = 0 the literal equivalence
    fails at n != 1. The paper and README state this openly and do not
    claim the degenerate cases. The Chinese source calls M_n(R) a
    noncommutative matrix ring, which also presupposes R != 0.
11. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All three PDF
    pages were opened and inspected after the final compilation; the
    third page contains only the two references.
