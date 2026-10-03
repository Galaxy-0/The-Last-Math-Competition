# Disproof of TLMC Conjecture 00000000057

**Verdict: FALSE.**

## The conjecture

Every n-vertex graph of minimum degree at least 3 contains Ω(log n / log log n)
cycles of pairwise distinct prime lengths.

## The attack

Counterexample family: **G_k = disjoint union of k copies of K_{3,3}**, n = 6k.

1. **Minimum degree 3.** Each vertex of K_{3,3} has degree exactly 3, and the
   disjoint union does not change degrees. So δ(G_k) = 3 ≥ 3 for every k, with
   n = 6k unbounded as k → ∞.

2. **All cycle lengths lie in {4, 6}.** K_{3,3} is bipartite with parts of size
   3, so every cycle alternates between the parts and has even length 2m with
   2 ≤ m ≤ 3 (length ≥ 4 since the graph is simple, length ≤ 6 since a cycle
   uses at most 3 vertices from each part). Hence every simple cycle has length
   4 or 6. This is preserved under disjoint union (every cycle lies inside one
   copy).

3. **No prime cycle lengths.** 4 = 2·2 and 6 = 2·3 are composite. Therefore the
   number of cycles of pairwise distinct prime lengths in G_k is **0 for every
   k**, while log n / log log n → ∞ as n = 6k → ∞. So the claimed Ω(log n /
   log log n) lower bound fails for every positive constant.

Brute-force check (reproduce.py): for k = 1, 2, 3, 5, 8 the enumerated cycle
lengths of G_k are exactly {4, 6} (k = 1: 9 four-cycles + 6 six-cycles up to
direction, 18 + 12 with orientation), and the count of distinct prime lengths
is 0, versus log n / log log n ≈ 3.07 already at n = 6 and growing without
bound.

## Boundary of validity

- The attack needs no assumption beyond min degree ≥ 3; connectivity was never
  part of the conjecture. If the conjecture were restricted to **connected**
  graphs, this family would not apply (each G_k has k components).
- The attack is the standard obstruction: degree conditions alone cannot force
  long or odd cycles. Any repair must either require connectivity or bound the
  number of components.
- For connected min-degree-3 graphs the conjecture remains untouched here.

## Files

- `main.tex` — write-up of the disproof (compiles with tectonic; PDF in `build/`).
- `reproduce.py` — standalone brute-force recomputation (`python3 reproduce.py`).
- `lean4/` — Lean 4 (core, no Mathlib, toolchain leanprover/lean4:v4.33.1)
  formalization: every cycle of G_k has even length ≥ 3, hence non-prime;
  every vertex has 3 distinct neighbors; n = 6k unbounded. Zero axioms,
  zero `sorry` (verified by `#print axioms` in `Check.lean`).

Build Lean:

```
cd lean4
export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build
lake env lean Check.lean
```
