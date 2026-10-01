# Disproof of TLMC Conjecture 00000000544

**Verdict: FALSE** — the "equality on forests" clause fails at the very first nontrivial forest.

## Conjecture (as stated)

Let `A_G` be the incidence matrix of a graph `G` and `I_{A_G}` the toric ideal it
generates; `Graver(I_{A_G})` is the Graver basis (all irreducible elements of the
lattice `ker_Z A_G`). The conjecture claims, for every graph without isolated vertices,

```
|Graver(I_{A_G})| <= Sum_{H subseteq G, H forest} 2^{|V(H)|},
```

**with equality attained on forests**.

## Attack: the single-edge forest `G = K_2`

`K_2` (two vertices joined by one edge) is a forest without isolated vertices, so the
conjecture requires equality there.

1. `A_{K_2} = [1; 1]` — a `2 x 1` unoriented incidence matrix whose single column is
   `(1, 1)^T`. (Oriented convention `(1, -1)^T` changes nothing below.)
2. The monomial map is `phi: k[x_1] -> k[t_1, t_2]`, `x_1 |-> t_1 t_2`, which is
   injective. Hence `I_{A_{K_2}} = 0`.
3. Equivalently the lattice `ker_Z A_{K_2} = { u in Z^1 : A u = 0 } = { u : u = 0 } = {0}`
   has no nonzero elements, so it contains no irreducible (Graver) elements:
   `Graver(I_{A_{K_2}}) = emptyset`, i.e. **`|Graver| = 0`**.
4. Right-hand side on `K_2` (spanning-subgraph reading of `H subseteq G`): the two
   spanning subgraphs (edgeless graph, `K_2` itself) are both forests with 2 vertices,
   so `RHS = 2^2 + 2^2 = 8`. Under any reading `RHS >= 2^2 = 4`, because `H = G = K_2`
   itself is a spanning forest contributing `2^{|V(H)|} = 4`.
5. Therefore `0 = |Graver| != RHS >= 4`: **the equality-on-forests claim fails**.

Stronger remark (why this is not a convention artefact): for *every* nonempty forest
the columns of the unoriented incidence matrix are linearly independent, so
`I_{A_G} = 0` and `|Graver| = 0`, while the RHS is `>= 2^2 = 4` whenever `G` has an
edge. Equality fails on every forest with at least one edge; `K_2` is the minimal
counterexample. Only the inequality half of the conjecture survives, and only trivially.

## Boundary of validity

- The upper-bound half `|Graver| <= RHS` still holds here (`0 <= 4 <= 8`); what is
  falsified is exactly the equality clause on forests.
- Graphs with a single vertex are excluded by the no-isolated-vertices hypothesis;
  `K_2` is the smallest admissible graph, so the counterexample is minimal and there
  is no smaller boundary to test.

## Reproduction

- `reproduce.py` — standalone recomputation (no dependencies): brute-forces the
  lattice `ker_Z A_{K_2}`, the Graver basis, and enumerates the forest subgraphs of
  `K_2`; prints `|Graver| = 0`, `RHS = 8` (spanning) and `0 != RHS`.
- `lean4/` — Lean 4 (v4.33.1, core only, **zero axioms, zero sorry**) formalization:
  `lake build && lake env lean Check.lean`; every theorem reported by
  `#print axioms` as *does not depend on any axioms*.
- `build/main.pdf` — write-up (compiled from `main.tex` with tectonic; see `build/log.txt`).

## Result summary

| quantity | value |
|---|---|
| `ker_Z A_{K_2}` | `{0}` |
| `Graver(I_{A_{K_2}})` | `emptyset` |
| `|Graver|` | `0` |
| `RHS` (spanning forests) | `8` (>= 4 under any reading) |
| equality `|Graver| = RHS` | **fails** |
