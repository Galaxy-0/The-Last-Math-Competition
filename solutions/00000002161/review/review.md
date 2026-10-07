# Solution Review — Conjecture 00000002161 (PR 682)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005175551`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read in both languages; `conjecture.md` is byte-identical to the official `conjectures/00000002161.md`.
- Change policy: only the declared submission folder is added; no metadata, conjecture, root, or unrelated files are changed.
- LaTeX: independently rebuilt with `latexmk -pdf` (exit 0). Shipped and rebuilt PDFs contain identical text after ligature/line-break extraction normalization.
- Lean: fresh `lake build` under Lean 4.19.0 / Mathlib `c44e0c8e...` succeeded with zero errors and zero warnings.
- Axioms: independent `#print axioms` on `not_per_graph_genus_one`, `not_class_minimum_one`, `counterexample_certificate`, and `path_positive_inertia` shows only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe definition, `implemented_by`, or `extern`; small finite checks use kernel-checked `decide`.
- Auxiliary code: the exact rational-arithmetic checker `auxiliary/verify.py` exited 0, reproducing the shipped certificate (Sturm sequence for t⁴−3t²+1 giving two positive and two negative roots, all 16 vertex subsets, the full dart/rotation/face certificate, and rejection of deliberately invalid certificates); `auxiliary/replay.py` exited 0 and `certificate.replay.json` matches `certificate.json`; the bespoke independent verifier (fresh build, strict replays, 207-declaration environment audit, nine dependency pins) also exited 0 under my run.
- Duplicate status: base metadata marks 00000002161 unproven and undisproven.

## Semantic audit
The conjecture states that the minimal genus of graphs attaining the tight inertia bound α = i₊ equals 1, apart from complete graphs, with the genus computed by the Euler formula of 2-cell embeddings. The submission retains the printed equality condition and exhibits the all-positive signed path P₄: connected (proved along the three edges), not complete (0 and 2 are nonadjacent), with α(P₄) = 2 computed exactly over all sixteen vertex subsets, and i₊(A) = 2 from the exact characteristic polynomial t⁴ − 3t² + 1 whose complete root multiset {(1+√5)/2, (√5−1)/2, and their negations} is proved by a polynomial identity (`path_charpoly_factorization`), counting positive roots with multiplicity. Thus the witness attains the printed tight bound exactly, satisfying the hypothesis rather than a strengthened or corrected version of it.

The genus computation is faithful to the source's Euler-formula definition. A `RotationSystem` encodes an orientable cellular embedding combinatorially: darts biject ordered adjacent pairs, reversal is a fixed-point-free involution, the rotation preserves tails with one cyclic orbit per vertex star, and connectedness is required; faces are orbits of ρλ, and `HasCellularGenus G g` requires V − E + F = 2 − 2g in integer arithmetic. The supplied certificate (six darts, λ = (0 1)(2 3)(4 5), ρ = (0)(1 2)(3 4)(5), single face orbit (0 2 4 5 3 1)) gives V − E + F = 4 − 3 + 1 = 2, hence g = 0 — the standard one-face planar embedding of a tree. Minimum genus 0 is then automatic over the naturals. This is the genuine 2-cell Euler formula, not a numeric surrogate; the disk-and-band realization theorem is cited and explained but not smuggled in as an axiom, and the report marks that formalization boundary explicitly.

The quantifier structure is handled correctly for both readings of "the minimal genus equals 1": as a per-graph claim (every eligible noncomplete tight graph has minimum genus 1) it is negated by `not_per_graph_genus_one` via the witness with minimum genus 0; as a class-minimum claim it entails the lower-bound clause that every eligible graph's minimum genus is at least 1, negated by `not_class_minimum_one` with the same witness. Restricting the universal clauses to connected noncomplete graphs only narrows the domain and keeps the counterexample valid. I independently confirmed the inertia computation (r² + s² = 3, rs = 1 for r = (1+√5)/2, s = (√5−1)/2) and the face permutation product.

## Issues found
None blocking.

## Verdict
APPROVED. The planar tight witness P₄ is genuine, completely certified, and decisively contradicts the asserted minimum genus 1 under both quantifier readings; the formalization is faithful to the printed equality and Euler-formula definitions, and all independent builds, axiom audits, and exact auxiliary checks pass.
