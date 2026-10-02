# Disproof of conjecture `00000002732`

**Verdict: FALSE — a flag complex with all links 0-dimensional and
chromatic number 4.**

## The conjecture (verbatim from `conjectures/00000002732.md`)

> Definition: The Szekeres–Wilf type in topological combinatorics:
> chromatic number versus local structure. Conjecture: The recursive
> inequality between the chromatic number χ(Δ) of a simplicial complex and
> link chromatic numbers: χ(Δ) ≤ 2 + max over links of χ, and the equality
> complexes are classified as independence complexes of odd graphs.

**Object consistency.** We attack exactly the displayed inequality with
the standard notions: proper coloring of a simplicial complex (distinct
colors on every face) and link of a vertex.

## The counterexample

Δ = the **flag complex** of the Grötzsch graph G = Mycielski(C₅) — 11
vertices (the C₅ v₀..v₄, clones u₀..u₄, apex w), 20 edges
(vᵢvᵢ₊₁, vᵢuᵢ₊₁, vᵢuᵢ₋₁, uᵢw). All facts kernel-certified:

1. **G is triangle-free** (`is_triangle_free`): no edge has a common
   neighbor. Hence every link of Δ is a **0-dimensional** complex (a set
   of vertices), χ(link) = 1, and the conjectured bound gives
   **χ(Δ) ≤ 2 + 1 = 3**.
2. **χ(Δ) = χ(G)**: in a flag complex every face is a clique of the
   1-skeleton, so a proper coloring of Δ is exactly a proper coloring of
   G (standard equivalence, cited in README/tex).
3. **χ(G) = 4**: no proper 3-coloring exists — exhaustive kernel check of
   all **3¹¹ = 177147** assignments (`no_3coloring`, ~3 min kernel
   evaluation) — while the exhibited coloring
   **(0,1,0,1,2, 0,1,0,1,2, 3)** is proper (`witness_proper`).

So χ(Δ) = 4 > 3 = 2 + max link χ: the recursion inequality fails, with
every link as simple as possible (dimension 0).

## Reproduce

`python3 reproduce.py` — builds the graph, checks triangle-freeness, runs
the same exhaustive 3-coloring search (and a 4-coloring search), and
prints the link analysis. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 5 theorems,
all `does not depend on any axioms` (structural match tables; the big
check under `maxHeartbeats 0` + `maxRecDepth 400000`).

## Boundary

Only the inequality is refuted. The equality-classification clause is not
addressed, and no claim is made about non-flag complexes.
