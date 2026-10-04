# Solution Review — Conjecture 00000003964 (PR 481)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004150936`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official statement claims a Cayley-diameter bound for **every** finite simple group. `SOURCE.md` is byte-identical to the official bilingual file.
- Path policy: pass — only the submitter's own new folder was added; clean-base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0 after two passes; 2 complete pages, no errors. I read the full report and independently extracted/rendered the PDF. It matches the shipped Tectonic PDF in content.
- Lean: `lake build` exited 0 and direct `lake env lean -DwarningAsError=true Main.lean` exited 0 for the pinned Lean 4.19/Mathlib project.
- Axioms: all ten principal results, including `conjecture_false`, use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: none shipped or needed. I independently recomputed primality, cycle distance, and both logarithm bounds.

## Semantic audit
The source does not exclude abelian simple groups. Since `1021` is prime, `Z/1021Z` is a genuine finite simple group. The singleton `{1}` generates it, and the corresponding undirected Cayley graph is the 1021-cycle. The potential `min(a,1021-a)` changes by at most one per edge, so every walk from `0` to `510` has length at least `510`; hence the actual graph diameter is at least `510`. Meanwhile `1021<2^10`, so both `3(ln 1021)^2≈144.014` and `3(log₂1021)^2≈299.746` are strictly below `510`.

The Lean theorem uses the actual `ZMod 1021` group, subgroup closure, Mathlib circulant/cycle graph, actual walks and shortest-path metric, and the finite maximum of all pairwise distances. It proves simplicity, generation, connectivity, the distance lower bound, both standard logarithm interpretations, and the negation of the universal claimed bound. The counterexample is non-vacuous. The unresolved PSL(2,p) clause is irrelevant because the universal upper-bound clause itself fails.

## Issues found
- none blocking. The report appropriately limits the result to the literal “every finite simple group” statement and does not claim to refute a nonabelian-only variant.

## Disposition
APPROVED — independent LaTeX/Lean reproduction passed with only standard axioms, and the formal prime-cyclic Cayley graph gives a decisive counterexample to the conjecture's universal diameter bound.
