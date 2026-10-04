# Disproof of conjecture 00000003476

In the complete graph K9 every edge has betweenness 1, which is below
9/4. Subdividing an edge raises the Wiener index from 36 to 53. So the
criterion "subdividing an edge decreases the Wiener index if and only
if its betweenness is below a quarter of the vertex count" fails. In
fact subdividing an edge never decreases the Wiener index of a
connected graph.

## Earlier submission

Pull request 225 (orionsheep) proposed the same kind of counterexample
with K5 and was closed without merging on 2026-10-03. The reviewer's
reason: its main Lean theorem was arithmetic on a hard-coded distance
list (a sum equal to 19, and 19 > 10), with no graph, Wiener index,
subdivision or betweenness defined in Lean. In addition, with
betweenness summed over ordered pairs an edge of K5 has betweenness
2 > 5/4, so K5 works only under some conventions. This submission
defines all four objects in Lean for arbitrary finite graphs, negates
the universally quantified criterion, and uses K9, which also covers
the ordered convention. main.tex has the full account.

## Reproduction

With Lean 4.19.0 and the supplied public-Git, commit-pinned dependencies:

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The cache command is optional if dependencies have already been built.
Compile main.tex with Tectonic or a compatible LaTeX installation.
No supplementary numerical program is needed.

## Scope and artifacts

SOURCE.md contains the exact bilingual source. main.tex/main.pdf contain
the complete proof. In Lean, graphs and distances are Mathlib's
SimpleGraph and SimpleGraph.dist. The subdivision is a graph on
Option V. The Wiener index is half the sum of distances over ordered
pairs. Betweenness is defined by counting the walks whose length equals
the distance and those among them that traverse the edge. The final
theorem negates the criterion quantified over all finite connected
graphs and all edges; a second theorem does the same with betweenness
summed over ordered pairs.

Lean proves that the Wiener index of the subdivided K9 is at least 45,
which exceeds 36 and is what the disproof needs; the exact value 53 is
computed by hand in the paper. The general statement that subdivision
never decreases the Wiener index, and the bipartite example K7,7, are
proved in the paper and are not formalised. No claim is made about the
phrase on the cut-load inequality chain.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed and
reviewed by a single AI agent; no independent review is claimed. No
custom axiom, sorry, admit or native_decide is used.
