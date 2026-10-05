# Adversarial self-review: conjecture 00000009611

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. No independent or
external review is claimed.

1. Reading. English and Chinese agree: the minimal size of a matrix
   realising a Perron number as an SFT entropy is an explicit function
   f(d) of the algebraic degree, and f(d) = d iff the minimal polynomial
   is sign-alternating. Claim (C1) is read literally: one function f
   works for every Perron number. Claim (C2) cannot be read literally,
   because its right-hand side depends on the number and not only on d;
   it is read per number: minimal size = degree iff sign-alternating.
   The paper says so.
2. Could (C1) mean something weaker, such as a bound? The source says
   "is an explicit function f(d)". Two numbers of the same degree with
   different minimal sizes refute any such function, explicit or not.
3. Realisation. The source defines entropy as log of the Perron
   eigenvalue of a nonnegative integer matrix and mixing SFTs. Lean
   defines Realizable through a primitive matrix (a positive power with
   k >= 1 is entrywise positive) and an eigenvalue with a positive
   eigenvector. The zero-size matrix is excluded and k = 0 is excluded
   (otherwise the 1 x 1 zero matrix would count as primitive). That such
   an eigenvalue is the spectral radius is proved
   (norm_le_of_isPerronEigenvalue), and that log of it is the growth
   rate of the number of paths is proved (hasEntropy_log). So upper
   bounds are genuine realisations.
4. Lower bounds are proved for a weaker hypothesis: any real eigenvalue
   with any nonzero real eigenvector of any nonnegative integer matrix
   of that size (IsEigenvalue). A realisation in the entropy sense gives
   such an eigenvalue by the Perron-Frobenius theorem; that theorem is
   not formalised and is not needed for the Lean statement, because
   Realizable already contains the eigenvector.
5. Hand check of x. p1(5/4) = -19/64, p1(2) = 5. A3 u = (x, x^2, 1 + x)
   for u = (1, x, x^2), equal to x u because x^3 = x + 1. A3^5 =
   [[1,1,1],[1,2,1],[1,2,2]] recomputed by hand and by a script.
   Sizes 1 and 2 are impossible because the degree is 3.
6. Hand check of y. p2(9/5) = -41/125, p2(2) = 2. w = (y, y^3 - 2y,
   y^2 - 2, 1); the four rows of A4 w = y w were checked by hand, the
   second using y^4 = 4y^2 + y - 4. Positivity needs y^2 > 2, true for
   y >= 9/5. A4^5 = [[6,1,12,8],[12,6,9,2],[1,4,6,8],[4,4,1,2]] was
   computed by a script; its positivity is kernel-checked in Lean. The
   characteristic polynomial of A4 is X^4 - 4X^2 - X + 4 =
   (X - 1)(X^3 + X^2 - 3X - 4): trace 0, sum of principal 2 x 2 minors
   -4, sum of principal 3 x 3 minors 1 and determinant 4 were checked
   by hand. This polynomial appears only in a remark; the Lean proof
   uses the eigenvector, not the characteristic polynomial of A4.
7. The key step: a 3 x 3 nonnegative integer matrix with eigenvalue y.
   Its characteristic polynomial is monic of degree 3 over Q and is
   divisible by the minimal polynomial p2 of degree 3, so they are
   equal; the X^2 coefficient is +1 = -trace, so trace = -1. Lean uses
   Mathlib's trace_eq_neg_charpoly_coeff. Irreducibility of p2 is
   needed here and is proved from the absence of rational roots; the
   six candidate values were recomputed by hand.
8. Perron numbers. Other roots of p1: mu^2 + x mu + x^2 - 1 = 0,
   discriminant 4 - 3x^2 < 0 for x >= 5/4, modulus squared x^2 - 1.
   Other roots of p2: mu^2 + (y+1) mu + y^2 + y - 3 = 0, discriminant
   13 - 2y - 3y^2 < 0 for y >= 9/5 (value at 9/5 is -0.32; this is why
   the interval starts at 9/5 and not at 3/2), modulus squared
   y^2 + y - 3 < y^2. Lean proves both through real and imaginary parts.
9. Sign criterion. WeaklySignAlternating forbids two adjacent
   coefficients of the same strict sign. X^3 - X - 1 has coefficients
   -1, -1 at degrees 0 and 1. Every stricter notion of alternation
   implies the weak one, so "minimal size = degree implies alternating"
   fails for each. The converse direction is refuted only on paper
   (X^3 - X^2 + X - 3: trace 1 forces the sum of principal 2 x 2 minors
   to be at most 0, but it is +1; the polynomial is irreducible and its
   real root dominates the complex pair because z^3 > 3). The paper
   marks this as not formalised.
10. Is this a technicality? No. The central claim is that the degree
    determines the minimal size. The obstruction, a negative trace of
    the minimal polynomial, is the classical reason why the degree is
    not enough, and it is the mathematical content of the example.
11. Alternative readings. Irreducible or arbitrary nonnegative integer
    matrices: same result, since lower bounds ignore primitivity and
    the examples are primitive. 0-1 matrices: A3 is 0-1, y needs size
    at least 4, and y is realised by a 0-1 edge matrix; stated on paper
    only. The exact minimal size of y for 0-1 matrices is not claimed.
12. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. `decide`
    is used only for the two matrix powers. The fresh build and direct
    Lean run are recorded in BUILD.json. All PDF pages were opened and
    inspected after the final compilation.
