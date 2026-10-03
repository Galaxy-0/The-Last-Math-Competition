# Disproof of conjecture `00000001681`

**Verdict: FALSE — in a rainbow-triangle-free coloring of K_n the number
of rainbow C₄s is identically 0: any rainbow C₄ would force a rainbow
triangle on its own four vertices. Since (1/24)·n² > 0 for every n ≥ 1,
the claimed lower bound — and with it the "optimal constant 1/24" —
fails on the entire class.**

## The conjecture (verbatim from `conjectures/00000001681.md`)

> Definition: Rainbow-triangle-free edge colorings are complete-graph
> colorings without triangles of three distinct colors. Conjecture: The
> number of rainbow C₄'s in such colorings is at least (1/24)·n²; the
> extremal configuration is attained by recursive constructions from
> balanced 4-partite colorings, and the constant 1/24 is optimal.

## The refutation

1. **Structural fact: no member of the class contains ANY rainbow C₄.**
   Suppose vertices v1v2v3v4 form a C₄ whose cycle edges carry four
   pairwise-distinct colors a, b, c, d (edges 12, 23, 34, 41). The
   coloring is of a COMPLETE graph, so the diagonal v1v3 has some color
   x. Triangle v1v2v3 is rainbow unless x ∈ {a, b}; triangle v1v3v4 is
   rainbow unless x ∈ {c, d}. Because {a, b} ∩ {c, d} = ∅, one of the
   two triangles is rainbow — contradiction. So the rainbow-C₄ count of
   every member, for every n, is exactly 0.

2. **Concrete exhibit, kernel-formalized: the constant 2-coloring.**
   Every 2-coloring lies in the class (a triangle's three edges drawn
   from two colors contain an equal pair, so no rainbow triangle), and
   no C₄ of a 2-coloring is rainbow (its four cycle edges drawn from
   two colors contain an equal pair, while a rainbow C₄ needs four
   pairwise-distinct colors). The Lean package exhibits this member for
   every n: the symmetric coloring `col a b = false`, with no rainbow
   triangle and no rainbow C₄ on any four distinct vertices.

3. **The bound fails numerically.** Count 0 against the claim
   "count ≥ (1/24)·n²" clears denominators to 24·0 ≥ n², i.e. 0 ≥ n²,
   which is false for every n ≥ 1 (n² > 0).

Conclusion: the minimum of the rainbow-C₄ count over the class is 0 for
every n ≥ 1, so no positive lower bound holds — the constant 1/24 is
not merely non-optimal, it is invalid, and the extremal-configuration
claim is vacuous.

## Verification

* `reproduce.py` — independent brute force: (i) no 3- or 4-tuple of
  Bool values is pairwise distinct (pigeonhole, exhaustive); (ii) the
  constant 2-coloring of K_n (n = 4..9) has zero rainbow C₄s and zero
  rainbow triangles; (iii) exhaustion of all K₄ colorings carrying a
  rainbow C₄ (cycle edges = permutation of 4 colors, both diagonals
  arbitrary) confirms each forces a rainbow triangle — 864 cases;
  (iv) (1/24)·n² > 0 for 1 ≤ n < 200 (exact fractions).
* Lean 4 (core, v4.33.1), `lean4/` — the pigeonholes for 3 and 4
  2-colored edges, the constant coloring's membership in the class and
  its lack of rainbow C₄s, and the arithmetic failure 24·0 < n·n, all
  combined in `conjecture_refuted`. All 10 audited theorems report
  `does not depend on any axioms`.

## Boundary

The refutation is complete for the stated bound clause: the count is 0
on the whole rainbow-triangle-free class, for every n ≥ 1 (point 1 is
a classical finite case argument on the K₄ spanned by the cycle; the
Lean kernel certifies the pigeonhole cores, the concrete 2-color
member, and the arithmetic; the general no-rainbow-C₄ reduction is
prose). The statement "count ≥ (1/24)·n² is attained by recursive
4-partite constructions" is thereby refuted as a lower-bound claim; no
position is taken on variant conjectures about other classes.
