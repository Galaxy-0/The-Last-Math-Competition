# Disproof of conjecture `00000000057`

**Verdict: FALSE — the 3-regular bipartite graphs G_k = disjoint union of
k copies of K_{3,3} have minimum degree 3 and contain ZERO cycles of
prime length, for every k, while n = 6k is unbounded.**

## The conjecture (verbatim from `conjectures/00000000057.md`)

> Conjecture: Every n-vertex graph of minimum degree at least 3 contains
> Ω(log n / log log n) cycles of pairwise distinct prime lengths.

## Object consistency

We attack the displayed universal statement with standard graph
definitions: a cycle is a simple cycle (pairwise distinct vertices,
cyclically adjacent), "prime lengths" refers to the standard primality
of cycle lengths, and Ω is the standard asymptotic lower bound.

## The counterexample family

Let G_k be the disjoint union of k copies of K_{3,3} (n = 6k vertices,
3-regular). For every k ≥ 1:

1. **Minimum degree 3.** Every vertex has exactly three neighbors (the
   three vertices on the other side of its K_{3,3}).
2. **G_k is bipartite.** Color each vertex by which side of its
   K_{3,3} it is on; every edge joins opposite colors.
3. **Every cycle length is even.** Walking around a cycle flips the
   color at each step and returns to the start, so the length is even
   (kernel-certified as a parity induction).
4. **No cycle has prime length.** A cycle has length ≥ 3, and the only
   even prime is 2. So the number of distinct prime cycle lengths is
   exactly 0 for every k.
5. **The family is unbounded in n.** n = 6k → ∞, and
   log n / log log n → ∞, so any Ω(log n / log log n) lower bound
   would in particular be ≥ 1 (a positive number of distinct prime
   cycle lengths) for all sufficiently large n. G_k has 0 for all k.

The K_{3,3} parity obstruction (bipartite ⇒ even girth ⇒ no odd cycles;
prime ≥ 3 ⇒ odd) kills the conclusion in the strongest possible way:
the count is not merely small, it is identically zero.

## Verification

* `reproduce.py` — builds K_{3,3} and its disjoint unions from scratch;
  checks 3-regularity, BFS 2-coloring (bipartiteness), and **exhaustively
  enumerates all simple cycles** of K_{3,3} (lengths are exactly
  {4, 6} — all even, none prime); confirms the count of distinct prime
  cycle lengths is 0 for k = 1..6 and prints the divergence of
  log n / log log n.
* Lean 4 (core, v4.33.1, no Mathlib) — `lean4/`: the 3-regularity, the
  color-flip edge lemma, the even-steps induction, the parity
  dichotomy, and the main theorem `no_prime_cycle` (no cycle of prime
  length, for EVERY k), plus `conjecture_refuted` (unbounded family).
  All 9 theorems report `does not depend on any axioms` (`#print
  axioms` audit in `Check.lean`). Everything about the graphs is proved
  uniformly in k — no finite instance stands in for the asymptotic
  claim; the only non-kernel step is the standard reduction from
  "count = 0 for an unbounded family" to the failure of an Ω(...) lower
  bound, stated in prose.

## Boundary

Only the displayed universal statement is refuted. Variants (e.g.,
minimum degree ≥ 4, or counting all even cycle lengths) are not
addressed.
