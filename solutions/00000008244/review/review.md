# Solution Review — Conjecture 00000008244 (PR 518)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004164947`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently; the report correctly targets the stated `2^d·d` maximal-agent bound.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. Shipped and rebuilt two-page PDFs have identical extracted semantic content and no TeX warnings.
- Lean: official pinned dependencies were linked; fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: final theorems use only `propext`, `Classical.choice`, and `Quot.sound`; two finite `decide` lemmas use only `propext`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied; all finite comparisons are formalized exactly.
- Base metadata marks the conjecture unsolved.

## Semantic audit
With alternatives at `0,2,3` and voters at `0,5/4,7/4`, negative squared-distance utilities yield strict orders
`a≻b≻c`, `b≻a≻c`, and `b≻c≻a`.
All three are distinct. The first order has left peak a; the other two have peak b, so every order increases toward its peak and falls away on both sides of the common axis. Thus the profile is single-peaked. The pairwise preference sets along the ordered voters are initial segments `{0}`, `{0,1}`, and `{0,1,2}` (with complements for reverses), so each pairwise preference switches at most once and the profile is single-crossing.

Both locations and preferences lie in real dimension one, where the conjectured bound is `2^1·1=2`. The profile has three agents—and even three distinct preference orders—so the bound is false. Median behavior is not the loophole: middle-voter peak b beats a 2–1 and c unanimously.

Lean defines the actual positions and utilities, proves preference comparisons from them for every voter/pair, verifies strict totality and distinctness, uses full all-pair definitions of single-peakedness and single-crossing, proves the median winner, computes actual real vector-space dimension one, and combines these facts into the strict bound failure.

## Issues found
None blocking.

## Verdict
APPROVED. A concrete one-dimensional simultaneously single-peaked and single-crossing profile has three distinct voters/preferences, exceeding the conjectured bound of two.
