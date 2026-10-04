# Adversarial self-review: conjecture 00000003842

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. No independent or
external review is claimed.

1. Reading. English: classes "of length at most l over an n-letter
   alphabet". Chinese: classes "of length l, letters at most n". The two
   differ (at most l versus exactly l). Both are formalised:
   classesUpToLength and classesOfLength, with claims
   ClaimedIdentityUpTo and ClaimedIdentityExact, and both are refuted.
   "Letters at most n" and "n-letter alphabet" are the same alphabet
   {1, ..., n}, modelled as Fin n with its linear order.
2. Empty word. classesUpToLength includes the class of the empty word.
   If a reader excludes it, the count drops by one. The refuting
   instances are strict inequalities in the same direction (7 < 20;
   l + 1 < l + 2 <= PP; n + 1 < n + 2 <= PP), so they survive. The
   paper says this.
3. Box orientation. PlanePartition a b c has a rows, b columns and
   entries at most c. The number of plane partitions in a box is
   symmetric in the three sides (a classical fact, not formalised), so
   the reading of "2 x n x l" does not affect the number. Hand check
   for the instances used: 2 x 2 x 2 is symmetric; for 2 x 1 x l the
   other orientations (1 x 2 x l, 1 x l x 2, ...) also give
   binom(l + 2, 2).
4. The monoid is the real one. Relations used: acb = cab (a <= b < c),
   bac = bca (a < b <= c), cadb = acbd (a <= b < c <= d),
   bdac = dbca (a < b <= c < d). This is the standard presentation of
   the hypoplactic monoid (plactic relations plus the two quartic
   relations). Independent check done outside the submission: a
   brute-force union-find over all words for n <= 3 and length <= 6
   gives class counts 1, 2, 4, 6, 8, ... for n = 2 and
   1, 3, 9, 19, 33, 51, 73 for n = 3, matching the count of quasi-ribbon
   tableaux sum_k binom(l-1, k-1) binom(n+l-k, l). In Lean the
   congruence is Mathlib's conGen on FreeMonoid, the quotient carries
   Mathlib's monoid structure, and knuth_instance and quartic_instance
   show that two nontrivial identifications really hold in it.
5. Lemma (length and short words). The relation "u = v, or both have
   the same length >= 3" is a congruence containing the generators; I
   rechecked compatibility with products by cases. In Lean this is an
   induction over ConGen.Rel (cases of, refl, symm, trans, mul).
   Consequence: words of length <= 2 are alone in their class. This
   does not depend on the exact relations, only on their lengths.
6. Counts of classes. For l <= 2 the class map is injective on words of
   length l, and the set of such words has n^l elements (Mathlib's
   card_vector). Classes of different length are disjoint, so
   H(n, 2) = 1 + n + n^2 and H(n, 1) = 1 + n. Over one letter a word is
   determined by its length, so h(1, l) = 1 and H(1, l) = l + 1 by
   induction. Hand check n = 2: words of length <= 2 are the empty
   word, 0, 1, 00, 01, 10, 11: seven.
7. Plane partitions. card_pp_222 is a kernel evaluation over the 81
   arrays; hand count: sum over (x, w) of (x - w + 1)^2 =
   1 + 5 + 14 = 20, and MacMahon's product gives 20. The lower bounds
   for 2 x 1 x l and 2 x n x 1 are by explicit injective families; the
   members were checked to be weakly decreasing in rows and columns and
   pairwise different.
8. Final statements. ClaimedIdentityUpTo and ClaimedIdentityExact
   quantify over all n and l and assert equality of Set.ncard of the
   class set with Fintype.card of the plane partitions. The class sets
   are finite, so ncard is the true cardinality. Both are refuted at
   (n, l) = (2, 2). The theorems one_letter and length_one show that
   the failure is not isolated.
9. Is the refutation a technicality? No relation is applicable to
   words of length <= 2, so the instance (2, 2) only counts words. That
   is the genuine content of the conjectured identity at that instance,
   and the reviewer of the earlier submission called it a genuine
   finite counterexample. The paper adds, as unformalised context, the
   true growth: H(2, l) is quadratic in l and PP(2, 2, l) quartic, so
   no reindexing of the same shape repairs the identity.
10. Earlier submission. Pull request 280: I read its description, the
    reviewer's comment and its Lean file at the head commit. The
    description of its error in main.tex, README.md and the content
    file is limited to what those show. What was right about it is
    acknowledged.
11. Not formalised (stated in the paper): exact binomial values,
    MacMahon's formula, symmetry of PP, the quasi-ribbon formula and
    table, the identification of the presentation with the tableau
    definition.
12. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All PDF pages
    were opened and inspected after the final compilation.
