# Parent review of conjecture 00000003841

Verdict: PASS for a proof of the source statement.

Reviewer: the coordinating AI agent that delegated this problem. This is an internal review
within the same workflow, not an external or independent peer review. No source file was
changed in review.

1. Source and reading. Both languages assert: a constant c(n) exists with at most |M|^c(n)
   surjective homomorphisms from the plactic monoid P_n to any finite monoid M, and the
   optimal exponent is at least 1 and unbounded in n. "Optimal exponent" is read as the least
   admissible real number. The draft proves that for n >= 1 the admissible reals are exactly
   those c >= n.
2. Objects. P_n is the quotient of Mathlib's `FreeMonoid (Fin n)` by the congruence generated
   by the two Knuth relations; homomorphisms are Mathlib monoid homomorphisms; the count is
   the cardinality of the subtype of surjective ones; exponents are Mathlib real powers.
3. Upper bound. A homomorphism is determined by the images of the n letter classes, which
   generate P_n. Checked by hand and in `hom_ext_gen`, `numSurj_le`.
4. Lower bound. In a commutative monoid both sides of each Knuth relation are products of the
   same three elements, so any assignment of the letters extends (`liftComm`). Into the cyclic
   group of prime order p, every assignment that is not identically zero is surjective, giving
   at least p^n - 1 surjections. For c < n a prime p >= 3 with p^(n-c) >= 2 gives
   p^n - 1 <= p^n / 2, impossible. Rechecked by hand.
5. Final statement. `Conjecture` is the conjunction of: an admissible exponent exists for
   every n; for n >= 1 a least admissible exponent exists and is at least 1; admissible
   exponents are eventually above any bound. `conjecture_true` proves it. The restriction
   n >= 1 in the middle clause is necessary (for n = 0 every real is admissible) and is stated.
6. Honesty of scope. The paper says plainly that the proof is elementary and uses only that
   P_n has n generators and that Knuth relations hold in commutative monoids. It also
   discusses the variant in which homomorphisms are counted up to automorphisms of M, which is
   not what the source states and is not formalised.
7. No earlier pull request exists for this conjecture.
8. Evidence. `validate_draft.py`: fresh build with warnings as errors, only `propext`,
   `Classical.choice`, `Quot.sound`, three PDF pages, no TeX warnings; recorded hashes match
   the files. All three rendered pages (prefix 5721caf757ac) were opened and inspected: no
   clipping, overflow or missing glyphs.
