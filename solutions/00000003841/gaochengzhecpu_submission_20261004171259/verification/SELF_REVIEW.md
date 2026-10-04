# Adversarial self-review: conjecture 00000003841

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. No independent or
external review is claimed.

1. Reading. English and Chinese agree: there is a constant c(n) such
   that the number of surjective homomorphisms from P_n to any finite
   monoid M is at most |M|^{c(n)}; the optimal exponent satisfies
   c(n) >= 1 and grows unboundedly in n. Formalised as: (i) for every n
   an admissible exponent exists; (ii) for n >= 1 the set of admissible
   real exponents has a least element and it is >= 1; (iii) for every
   real B there is N such that for n >= N every admissible exponent is
   >= B. (iii) is stronger than "unbounded".
2. Real versus integer exponents. The source does not say c(n) is an
   integer. IsAdmissible uses a real exponent and Real.rpow. The
   theorem isAdmissible_iff covers integers as a special case: the
   least admissible integer is also n.
3. Objects. The plactic monoid is Mathlib's quotient of FreeMonoid
   (Fin n) by conGen of the Knuth relations acb = cab (a <= b < c) and
   bac = bca (a < b <= c); I rechecked these against the standard
   statement of the Knuth relations. Homomorphisms are MonoidHom
   (identity-preserving); a surjective multiplicative map between
   monoids preserves the identity anyway, so nothing is lost.
   numSurj is Nat.card of the subtype of surjective homomorphisms; the
   type of homomorphisms to a finite monoid is proved finite, so
   Nat.card is the true count.
4. Upper bound, checked by hand: a homomorphism is determined by the
   images of the n letter classes, giving at most |M|^n homomorphisms;
   |M| >= 1 so |M|^n <= |M|^c for c >= n.
5. Lower bound, checked by hand. Commutative monoids satisfy both
   Knuth relations (same multiset of three factors on both sides). For
   M = Z/p and g not identically zero, g(i) = a != 0, every b equals
   k a with k the representative of b a^{-1}; so the image of the
   k-th power of the letter class is b. Lean proves a a^{-1} = 1 from
   ZMod.mul_inv_eq_gcd and primality, without a field instance.
   Distinct g give distinct homomorphisms. Hence at least p^n - 1
   surjective homomorphisms; Lean states this as
   p^n <= numSurj + 1 to avoid subtraction.
6. The contradiction for c < n, checked by hand: with delta = n - c,
   a prime p >= 3 with p >= 2^(1/delta) gives p^delta >= 2, hence
   p^c <= p^n / 2; then p^n - 1 <= p^n / 2 forces p^n <= 2, but
   p^n >= p >= 3 as n >= 1. In Lean the last step is nlinarith from
   p^n = p^c * p^delta, p^delta >= 2, p^c > 0, p^n - 1 <= p^c,
   p <= p^n, p >= 3.
7. n = 0. P_0 is trivial; numSurj is 1 for a trivial M and 0
   otherwise, so every real c is admissible and no least exponent
   exists. Clause (ii) is therefore stated for n >= 1, matching the
   source's alphabet {1, ..., n}. The paper and README say so.
8. Is the result a technicality? The proof is elementary and uses only
   that P_n has n generators and abelianises onto a free commutative
   monoid. That is stated plainly in the paper. The statement of the
   source is nevertheless exactly this counting bound, and the theorem
   determines the optimal exponent, not just its existence.
9. Alternative reading not covered: the label says "quotient count".
   Counting surjections up to Aut(M) changes the numbers: the optimal
   exponent then lies in [n - 1, n] and is 0 at n = 1 (a finite cyclic
   monoid has, up to automorphism, one generator). Under that reading
   the clause c(n) >= 1 would fail at n = 1 and hold from n = 2 on.
   Both language versions say "number of surjective homomorphisms", so
   the submission follows the statement; the variant is disclosed and
   not formalised. I rechecked the cyclic-monoid claim by cases on the
   index r of the monoid (r = 0 group; r = 1 group with an adjoined
   identity; r >= 2 only x generates).
10. Universe. IsAdmissible quantifies over monoids M : Type. Every
    finite monoid is isomorphic to one on Fin k, so this is no
    restriction.
11. No earlier pull request for this conjecture appears in the snapshot
    of all pull requests.
12. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All PDF pages
    were opened and inspected after the final compilation.
