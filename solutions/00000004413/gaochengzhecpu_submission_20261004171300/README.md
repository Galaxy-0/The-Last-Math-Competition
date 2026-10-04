# Disproof of conjecture 00000004413

The source claims that in a graph limit with degree bound d the measure
of cycles of length l is at most (d-1)^l / (2l), and that this bound is
attained and optimal for the d-regular tree. For d = 2 the bound is
false: the cycle graph C_l has all degrees 2 and cycle measure
1/l > 1/(2l), for every l >= 3. For d >= 3 the bound holds but is
neither attained nor optimal (every graph limit satisfies the stronger
bound d (d-1)^(l-2) / (2l), which is at most 3/4 of the claimed one),
and for no d >= 2 does the tree attain it, since a tree has no cycles.

## Earlier submission

Pull request 302 (orionsheep) treated this conjecture with the triangle
K3, the case l = 3 of the example used here. It was closed without
merging on 2026-10-03 together with a comment of its author withdrawing
the submission; the thread contains no reviewer verdict. Its example and
conclusion were correct. Its Lean file was read: it used a graph
structure of its own and counted closed sequences Z/n -> V with adjacent
consecutive values, not required to be injective, identified by their
edge sets. For n = 3 these are the triangles, so the instance used was
sound; for n >= 4 they include closed walks that are not cycles (for
example a, b, a, b on one edge), so the universally quantified statement
negated there was not the bound for cycles in general. This submission
uses Mathlib's SimpleGraph and cycleGraph, counts genuine cycles,
proves the violation for every l >= 3, and separates what holds for
d >= 3. main.tex has the full account.

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
the complete argument. In Lean, graphs are Mathlib's SimpleGraph, the
degree is SimpleGraph.degree and the cycle graph is
SimpleGraph.cycleGraph. CycleCopy G L is the type of injective graph
homomorphisms from cycleGraph L to G (rooted oriented cycles of length
L), and cycleMeasure G L is their number divided by 2L and by the number
of vertices. ClaimedUpperBound states the bound for all finite graphs,
all d and all L >= 3; conjecture_false is its negation, and
conjecture_false_every_length gives a violating graph of maximum degree
2 for every L >= 3.

Limits of the formalisation. Lean treats finite graphs, which are
special bounded-degree graph limits (limits of constant sequences);
general graph limits are not formalised. Lean proves that the cycle
measure of C_L is at least 1/L; the equality, the general upper bound
d (d-1)^(L-2) / (2L), the statement that the bound is true but not
optimal for d >= 3, and the statement about the regular tree are proved
in the paper only. The Lean refutation is at d = 2; for d >= 3 the
first clause of the source is true and the conjecture fails through its
second clause, which is a paper argument.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed by a
delegated AI agent with a self-review; the coordinating agent reviews
it separately. No independent or external review is claimed. No custom
axiom, sorry, admit or native_decide is used.
