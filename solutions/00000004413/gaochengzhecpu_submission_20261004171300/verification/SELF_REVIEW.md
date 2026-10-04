# Adversarial self-review: conjecture 00000004413

Verdict: PASS with stated limits, after a separate mathematical and source-correspondence pass.
This problem was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. No independent or
external review is claimed.

1. Reading. English and Chinese agree: for a bounded-degree graph limit
   the count (measure) of cycles of length l is bounded above by
   (d-1)^l / (2l), d the degree bound, and the bound is attained and
   optimal for the d-regular tree limit. Two clauses: (i) the upper
   bound, (ii) attainment and optimality.
2. Finite graphs are graph limits. A finite graph with uniform random
   root is a unimodular random rooted graph and the Benjamini-Schramm
   limit of its constant sequence. Its cycle measure is
   (#cycles of length l) / |V|, which equals E[N_l] / (2l) with N_l the
   number of rooted oriented cycles at the root. So a finite
   counterexample to (i) is a counterexample among graph limits. Lean
   formalises finite graphs only; this is stated in the paper, README
   and content file.
3. Normalisation. Other natural normalisations (expected number of
   l-cycles through the root = l * c_l; probability that the root lies
   on an l-cycle = 1 for C_l) are at least as large on the example, so
   the violation does not depend on the choice.
4. The example, by hand. C_l (l >= 3) is 2-regular and contains exactly
   one cycle of length l, so c_l = 1/l. The claimed bound with d = 2 is
   1/(2l). 1/l > 1/(2l). For l = 3 this is the triangle: 1/3 > 1/6.
5. Lean objects. Mathlib's SimpleGraph, SimpleGraph.degree and
   SimpleGraph.cycleGraph; degree 2 is Mathlib's
   cycleGraph_degree_three_le. Cycles of length L in G are counted as
   injective homomorphisms cycleGraph L ->g G divided by 2L. For
   L >= 3 this is the number of L-cycle subgraphs because the
   automorphism group of C_L has order 2L (start vertex and direction).
   The count is Nat.card of a type proved finite.
6. Lower bound in Lean. 2L injective homomorphisms C_L -> C_L are
   exhibited (L rotations, L reflections) and proved pairwise different;
   the key fact is 1 + 1 != 0 in Fin (l + 3). So the count is >= 2L and
   the measure >= 1/L. Lean does not prove equality; the disproof does
   not need it.
7. Final statement. ClaimedUpperBound quantifies over all finite graphs,
   all d, all L >= 3. The refutation instantiates d = 2, L = 3 and
   Mathlib's cycleGraph 3; conjecture_false_every_length does it for
   every L >= 3. The expression (d-1)^L / (2L) is negative for d = 0 and
   odd L, which would give a degenerate refutation; it is not used.
8. Is d = 2 a technicality? Proposition 2 of the paper (by hand:
   N_l <= d (d-1)^(l-2), checked by building the sequence step by step)
   shows clause (i) is TRUE for d >= 3, because
   d (d-1)^(l-2) <= (3/4) (d-1)^l there. So the upper bound fails only
   at d = 2 (graphs whose components are paths and cycles). The source
   places no restriction on d, so d = 2 is a legitimate instance, but a
   reviewer may weigh this. The conjecture also fails for every d >= 3
   through clause (ii): the bound is not attained (strictly smaller
   true bound) and the tree, having no cycles, has measure 0. That part
   is on paper only. This is the main limit of the submission and is
   stated plainly in the paper and README.
9. Clause (ii) not formalised. Mathlib's IsAcyclic lives in a module
   that is not available in the cached build, and the infinite regular
   tree is not a finite graph; the statement "a tree has no cycles" is
   left to the paper.
10. Earlier submission. Pull request 302: I read its description, its
    comment thread (one comment, by the author, withdrawing it) and its
    Lean file at head commit 675d27ba. The account in main.tex,
    README.md and the content file is limited to that: withdrawn, no
    reviewer verdict; example correct; its cycle-walk definition does
    not require distinct vertices, which is harmless for n = 3 and
    wrong for n >= 4 (checked: a, b, a, b satisfies its IsCycleWalk on
    a single edge).
11. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All PDF pages
    were opened and inspected after the final compilation.
