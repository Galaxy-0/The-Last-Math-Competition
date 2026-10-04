# Adversarial self-review: conjecture 00000002305

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed and reviewed by a single AI agent. No
independent or external review is claimed.

1. Reading. Both source languages state k(G) >= c [G:H] "for maximal H"
   with c = 1/2 and place no restriction on G. The submission reads this
   as: every finite group, every maximal subgroup. The paper states this
   reading and names the one it does not address (H only some maximal
   subgroup; the normal subgroup of order 31 has index 5 and satisfies
   the inequality).
2. The epsilon variant. The source does not define epsilon(G). The paper
   does not invent a definition. fails_above proves failure for every
   constant c > 11/31, i.e. for (1/2)(1 - epsilon) whenever
   epsilon < 9/31, and claims nothing beyond that.
3. The group is real. G is a structure with fields in ZMod 31 and ZMod 5.
   All group axioms are proved from tw_add and tw_zero, which are
   kernel-checked over all residues. act_one, act_mul and act_faithful
   show it is exactly the group of the 155 affine maps x -> 2^k x + a.
   The inverse formula was checked by hand against the composition law.
4. Order and index. card_G uses an explicit equivalence with
   ZMod 31 x ZMod 5. card_H uses an explicit equivalence of the subgroup
   with ZMod 5. index_H then follows from Mathlib's Lagrange identity
   card * index = card. No value is assigned by definition.
5. Maximality. IsCoatom in Subgroup G is the standard notion: H is not
   the whole group, and every strictly larger subgroup is the whole
   group. The proof uses only Lagrange and the primality of 31. The case
   |K| = 5 is excluded by H <= K and equal cardinality, not by assumption.
6. Class number is exact. exists_rep covers every element: the cases
   k != 0, (k = 0, a != 0) and the identity are exhaustive. The two
   existence lemmas are kernel-checked over all of ZMod 31 and ZMod 5.
   label_conj proves the label is a class function using the general
   conjugation formula conj_a, which is proved algebraically.
   label_rep separates the eleven representatives. Hence the map from
   the index type onto ConjClasses G is a bijection and the count is 11,
   not merely at most 11. Hand check: 4*31 + 1 + 6*5 = 155.
7. The index type has cardinality 1 + 6 + 4 = 11, kernel-checked.
8. The final statement. ClaimedBound quantifies over every Type-level
   finite group and every coatom of its subgroup lattice, with the
   inequality in Q. Nat.card of ConjClasses is the number of conjugacy
   classes for a finite group. conjecture_false instantiates it at G, H.
9. The margin is not thin: 11 versus 15.5. No rounding is involved.
10. Remark on the family C_p : C_q is clearly labelled as not formalised
    and not used. Its class count q + (p-1)/q was rechecked by hand, and
    it gives 11 for (p, q) = (31, 5) and p for q = p - 1.
11. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. Both PDF pages
    were opened and inspected after the final compilation.
