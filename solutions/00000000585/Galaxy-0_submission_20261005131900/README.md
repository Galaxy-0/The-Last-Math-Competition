# Conjecture 00000000585

For every finite undirected multigraph G, including loops and parallel edges,
and every natural q >= 2:

    T_G(q+1,q-1) >= q^(r(E)) > 0.

An explicit, duplicate-free finite family of decorated edge subsets has
exactly this cardinality. This includes every prime power q.

## Reproduce

Use the official Lean 4.31.0 toolchain pinned in `lean-toolchain`:

    lake build
    lake env lean Tutte585.lean
    lake env lean Examples.lean
    python3 check_model.py

No Mathlib or third-party Lean dependencies are required. `lake build`
compiles both the proof and the example module. `Examples.lean` includes
kernel-checked computations for the empty graph, a loop, an ordinary edge,
a parallel pair, a triangle, and its explicit object count.

To build the report on a standard TeX installation, run `pdflatex solution.tex`
twice. `build_pdf.sh` additionally supports the supplied cloud image whose
TeX sources are installed without a prebuilt format or font search index.
It uses installed TeX sources and fonts only; it downloads nothing.

## Verification

- Official Lean 4.31.0 (release commit
  `68218e876d2a38b1985b8590fff244a83c321783`).
- Clean `lake build`, direct source check, and example check succeeded.
- Main theorem axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
- No added axioms, proof placeholders, or `native_decide`.
- Independent Python regression suite passed 753 graph/parameter cases,
  covering loops, parallel edges, empty/disconnected graphs, q=2, rank
  comparisons, positive lower bounds, and unique decorated objects.
- Three-page PDF built from the supplied LaTeX and visually inspected.

The Python checks supplement, and do not replace, the Lean proof.

## Definitions and scope

The graph model contains finite vertices and individually labeled edge
positions. Connectivity is the inductive undirected reachability relation.
An executable finite-cut algorithm is proved equivalent to it. Component
count counts the least vertex of each component; rank is |V|-components.
The Tutte function is the standard rank-subset definition on x,y >= 1.

`conjecture_00000000585` proves positivity, equality to the length of an
explicit finite enumeration, and absence of duplicates. All defining
algorithms are executable. Classical reasoning occurs only in the proof
that the cut test is equivalent to connectivity.

The elementary facts r(A) <= r(E) and r(A) <= |A| are proved in the written
report and justify the natural-number exponents. They are not separate Lean
lemmas. The source makes no claim about an unspecified log-concavity
property mentioned only in the conjecture's introductory descriptor.

## Official source

https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/d7d4bc9f6918401d3fb22c6e473df63eba5dbb78/conjectures/00000000585.md

Fresh eligibility check on 2026-10-05 at 13:17 UTC, upstream main
`ba46ce0997cbf232fe95e5dced37ff4d32e1eb94`: metadata unsolved, no solution
folder for this identifier, and exact-ID PR search returned zero results.
