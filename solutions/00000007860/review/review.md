# Solution Review — Conjecture 00000007860 (PR 448)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004112832`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; `SOURCE.md` is byte-identical to `conjectures/00000007860.md`.
- Change policy: only the declared submission folder is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt PDFs both contain two complete pages with matching semantic text after ligature/spacing extraction normalization; the recorded shipped-PDF hash matches.
- Lean: fresh build under Lean 4.19.0/Mathlib `c44e0c8e...` passed, as did direct `lake env lean -DwarningAsError=true Main.lean`.
- Axiom audit: all nine printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, or kernel-check bypass occurs.
- Auxiliary program: `verify.py` exited 0 and exactly executed the one-vertex witness. Its result was independently checked: one order, one greedy color, chromatic number one, zero pointwise waste, zero uniform expectation, and `1/2 - sqrt(1/2)<0`.
- Base metadata marks the conjecture unsolved.

## Semantic audit
The statement asserts a waste bound “for every graph,” with no lower bound on the vertex count in either language. Let G be the one-vertex edgeless graph. Its unique uniform order assigns first-fit color 0 to the sole vertex, so the number of distinct colors used is 1. The constant coloring is proper and no zero-color coloring of a nonempty vertex set exists, so χ(G)=1 and W(G)=0. But `1/2 - sqrt(1/2) < 0`, hence the claimed universal upper bound is false. The same zero value is the uniform expected waste because the permutation sample space has size one. Thus the disproof covers both a pointwise-random-variable reading and an expectation reading.

The Lean witness is genuine and non-vacuous: `singletonGraph` is Mathlib's bottom simple graph on `Fin 1`; permutations are `Equiv.Perm`; `firstAvailable` uses the least natural outside a finite forbidden set; `greedyRun` filters actual processed adjacencies; the color count is the image finset's cardinality; and `chromaticNumber` is Mathlib's minimum proper-coloring number. The singleton execution, chromatic number, zero waste, one-element permutation space, zero expectation, negative real bound, and final universal negations are all proved rather than assumed. Refuting one universal conjunct suffices; the report accurately leaves the unrelated random-graph asymptotic and extremizer claims unresolved.

## Issues found
None blocking.

## Verdict
APPROVED. The singleton is a concrete counterexample to the unqualified universal inequality, both interpretations are formally refuted, all builds and auxiliary checks reproduce, and only standard foundational axioms are used.
