# Adversarial self-review: conjecture 00000002604

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed and reviewed by a single AI agent. No
independent or external review is claimed.

1. Reading. English: distributive lattices with the same layer-count
   vector are isomorphic. Chinese: the count vector of the coatom layers,
   i.e. layers counted from the top. Both are formalised: rank functions
   (zero at the bottom) and corank functions (zero at the top), each tied
   to Mathlib's covering relation. The common vector (1,2,2,2,1) is a
   palindrome, so the two readings agree on this example; layer 1 of the
   corank is the set of coatoms, so the number of coatoms also agrees.
2. The objects are lattices. L1 is Fin 4 x Fin 2 with Mathlib's own
   product DistribLattice instance. L2 is a subtype of Fin 3 x Fin 3;
   closure under sup and inf is kernel-checked over all pairs, and the
   lattice structure is Mathlib's Subtype.lattice, so sup, inf and order
   are the ambient ones. Distributivity is inherited from the ambient
   lattice by the ambient inequality, not assumed.
3. Rank functions. IsRankFunction requires g(bot) = 0 and
   g(b) = g(a) + 1 for every covering pair. For both lattices this is
   kernel-checked over all pairs in the unfolded form of the covering
   relation and then transferred to Mathlib's CovBy. Hand check for L2:
   the only removed point is (2,0); every pair with (2,0) strictly
   between also has (1,0) or (1,1) strictly between, so no covering
   relation of L2 skips a rank.
4. Layer counts. The five layer sizes of each of the four functions are
   kernel-checked to be 1,2,2,2,1, and equality for every natural k is
   proved (k < 5 by cases, k >= 5 because all values are below 5).
   Hand table rechecked: L1 layers (0,0) | (1,0),(0,1) | (2,0),(1,1) |
   (3,0),(2,1) | (3,1); L2 layers (0,0) | (1,0),(0,1) | (1,1),(0,2) |
   (2,1),(1,2) | (2,2).
5. Non-isomorphism is a statement about all order isomorphisms:
   IsEmpty (L1 ≃o L2). The proof transports the five witnesses of L2
   through the inverse of a hypothetical isomorphism and uses that order
   isomorphisms preserve and reflect both < and <=. The two facts about
   L1 are kernel-checked over all triples of L1. This is the step that
   the earlier submission did not establish.
6. Earlier submission. Its Lean file was read at the upstream commit that
   added it. The quoted theorem uses List.all with "= false", which is
   the negation of "all bijections are isomorphisms". The description of
   this error in main.tex, README.md and the PR text is limited to what
   the file and the organisers' re-audit commit message show. Its
   mathematical example is acknowledged as correct and is the same pair
   of lattices up to isomorphism.
7. Final statements. ClaimedCoatomLayerRigidity and ClaimedRankRigidity
   quantify over all finite bounded distributive lattices, all corank
   (rank) functions and equal layer counts for every k, and conclude
   Nonempty of order isomorphisms. Both are refuted by instantiation.
8. Scope. Only the first clause is refuted. The Kruskal-Katona clause is
   not addressed. The Birkhoff identification with ideal lattices is a
   remark, rechecked by hand, and is not used.
9. No sorry, admit, native_decide, opaque or custom axiom. The printed
   axioms are propext, Classical.choice and Quot.sound only. The fresh
   build and direct Lean run are recorded in BUILD.json. All three PDF
   pages were opened and inspected after the final compilation.
