# Adversarial self-review: conjecture 00000002311

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. No independent or external
review is claimed.

1. Reading. Both source languages make two assertions: the derangement
   proportion of a transitive group is at least c/|Omega| with c = 1/2,
   and the tightness of "the corrected constant" is verified by Frobenius
   groups. The Chinese text matches the English one. The only constant
   named is 1/2, so "the corrected constant" is read as 1/2; the paper
   says so and says what follows if another constant were meant. The
   first assertion is true. The submission is a disproof of the
   statement as a whole through the second assertion, and the paper,
   README and content file say this plainly.
2. What "tight" means. Three readings are stated as Lean propositions
   and each is refuted for c = 1/2: the constant cannot be enlarged
   (CannotBeImproved), a Frobenius group attains equality
   (AttainedByFrobenius), Frobenius groups come arbitrarily close
   (ApproachedByFrobenius). Conjecture is the bound together with the
   disjunction of the three, so its negation does not depend on choosing
   one reading. corrected_statement shows that all three hold for c = 1,
   so the definitions are not vacuous.
3. The general fact asked for by the reviewer of the earlier submission.
   cameron_cohen is quantified over every type G with a group structure,
   every MulAction on every type, Finite G, Finite Omega, transitive,
   degree at least two. It therefore covers every Frobenius group, not
   one example. frobenius_card_derangements gives the exact count n - 1
   for every Frobenius action.
4. Proof of the bound, checked by hand. Burnside on Omega gives
   sum fix = |G|. On Omega x Omega the fixed points of g are pairs of
   fixed points (fixedByProdEquiv), and the diagonal point (a,a) and
   (a,b) with a != b are in different orbits because g a = a and
   g b = a force a = b; so sum fix^2 >= 2|G|. Pointwise,
   fix^2 + n <= (n+1) fix + n [fix = 0] for 0 <= fix <= n. Summing gives
   |G| <= n |D|. Test: S3 on 3 points has fix values 3,1,1,1,0,0, sums 6
   and 12, and 3 * 2 = 6 = |G|. Test: AGL(1,7) has 6 derangements and
   7 * 6 = 42 = |G|. Test: C31:C5 on 31 points has 30 derangements and
   31 * 30 = 930 >= 155.
5. Degree one. For |Omega| = 1 there are no derangements and the bound
   fails for every positive constant. LowerBound assumes degree at least
   two, which gives the source its best case; the disproof does not use
   the degenerate case.
6. Faithfulness. The theorems do not assume a faithful action, so they
   are more general than statements about permutation groups. In
   IsFrobenius, faithfulness follows from the other fields (an element
   acting trivially fixes two points).
7. The Frobenius definition. Mathlib has no Frobenius groups. The
   structure uses the standard permutation-group definition: transitive,
   degree at least two, only the identity fixes two points, some
   non-identity element fixes a point. The last field excludes regular
   actions. Frobenius' theorem on the kernel is not needed and not
   claimed.
8. The example. Equiv.Perm (Fin 3) acts on Fin 3 by Mathlib's
   applyMulAction. Transitivity is proved with swaps. The two Frobenius
   conditions are kernel-checked over all six permutations. The
   proportion 1/3 is derived from the general Frobenius count and the
   order 6, not assigned.
9. Objects. Group, MulAction, IsPretransitive, fixedBy, orbitRel and the
   Burnside lemma are Mathlib's. derangements and derangementProportion
   are defined in the file directly from the action; cardinalities are
   Nat.card and the proportion is a quotient in Q.
10. Earlier submission. The pull request body, the reviewer's closing
    comment and the Lean file (from the patch of the pull request) were
    read. The quoted theorem is verbatim. The description is limited to
    these sources, and the correctness of its computation is
    acknowledged.
11. Not formalised: the remark (stabiliser order divides n - 1, equality
    exactly for sharply 2-transitive groups, the Boston-Shalev theorem).
    None of it is used.
12. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All four PDF
    pages were opened and inspected after the final compilation; no
    clipping or overflow, and the compiler reported no warnings.
