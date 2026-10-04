# Parent review of conjecture 00000009611

Verdict: PASS.

Reviewer: the coordinating AI agent that delegated this problem. This is an internal review
within the same workflow, not an external or independent peer review. No source file was
changed in review.

1. Source and reading. Both languages assert that the minimal size of a nonnegative integer
   matrix realising a Perron number as a mixing-SFT entropy is a function f(d) of its
   algebraic degree d, and that f(d) = d exactly when the minimal polynomial is
   sign-alternating. The first clause is taken literally; the second is read for each number
   separately, because its right-hand side depends on the number.
2. Objects. Matrices, characteristic polynomials and minimal polynomials are Mathlib's.
   `Realizable` asks for a primitive matrix with natural-number entries and an entrywise
   positive eigenvector; the file proves that such an eigenvalue bounds the modulus of every
   complex eigenvalue and that log(path count)/k tends to its logarithm, so it is the Perron
   eigenvalue and the exponential of the entropy. `IsPerronNumber` is the usual definition
   through the complex roots of the minimal polynomial.
3. The two numbers. I rechecked by hand: p1 = X^3 - X - 1 and p2 = X^3 + X^2 - 3X - 4 have no
   rational roots; p1(5/4) < 0 < p1(2) and p2(9/5) < 0 < p2(2); the quadratic cofactors have
   negative discriminant and their roots have squared modulus x^2 - 1 and y^2 + y - 3, below
   x^2 and y^2. The eigenvector identities for both matrices, including
   y^4 = 4y^2 + y - 4, are correct, and both matrices have a positive fifth power.
4. Lower bound. A real eigenvalue of an integer matrix is a root of its characteristic
   polynomial, so its minimal polynomial divides it; in size 3 the two cubics coincide and the
   trace would be -1. This excludes every nonnegative integer 3x3 matrix, primitive or not.
5. Final statements. `ClaimedDegreeLaw` asserts a function f with minimal size f(degree) for
   every Perron number; `conjecture_false` refutes it from f(3) = 3 and f(3) = 4.
   `conjecture_false_realized` does the same over all realised numbers and does not depend on
   the definition of Perron numbers. `sign_criterion_false` refutes one direction of the
   second clause for the weakest notion of sign alternation.
6. Limits, stated in the paper: Lind's theorem and the Perron-Frobenius existence theorem are
   not formalised and not used; the converse direction of the second clause and the 0-1
   matrix variant are paper-only remarks; a reading of the first clause as an upper bound
   only is not addressed.
7. No earlier pull request exists for this conjecture.
8. Evidence. `validate_draft.py`: fresh build with warnings as errors, only `propext`,
   `Classical.choice`, `Quot.sound`, five PDF pages, no TeX warnings; recorded hashes match
   the files. All five rendered pages (prefix 474c8d01d509) were opened and inspected: no
   clipping, overflow or missing glyphs; the last page holds only the end of the
   reproduction section.
