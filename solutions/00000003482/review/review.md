# Solution Review — Conjecture 00000003482 (PR 656)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005081033`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — existence of graph families with χ−χ_f > n^{1/3}, and the order clause "the maximal order of deviation is n over the logarithm squared"; the submission's `conjecture.md` is byte-identical to `conjectures/00000003482.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode` (exit 0); shipped/rebuilt text matches up to font-subset extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: no executable `sorry`, `native_decide`, axiom declarations, `unsafe`, `implemented_by`, `extern`; all hits are prose. `decide` is used only on `Fin 5` facts.
- Axioms: independent run — `maxGap_not_isBigO`, `maxGap_not_isTheta`, `maxGap_not_isEquivalent`, `not_isBigO_of_isLittleO` use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: the fractional-colouring weights and the 3-colour lemma were re-derived by hand and are correct.

## Semantic audit
The conjecture's order clause reads "the maximal order of deviation is n/(log n)²". The submission formalizes M(n) = max over all graphs on n vertices of χ(G) − χ_f(G) — `maxGap n = ⨆ G : SimpleGraph (Fin n), gap G` with `gap G = χ(G).toNat − χ_f(G)` (toNat is justified: χ(G) ≤ |V| < ∞ is proved) — and refutes M(n) = O(n/(log n)²), = Θ(...), and ∼ ..., which covers every upper-bound reading of "maximal order". The pure lower-bound reading M = Ω(n/(log n)²), the ratio reading χ/χ_f, and the (true, hence unrefutable) existence clause are honestly scoped out.

χ_f is defined by the standard linear program: `IsFracColoring G w` requires w ≥ 0, w = 0 off independent sets, and coverage Σ_{S∋v} w(S) ≥ 1 for every vertex; `fracChromaticNumber` is the infimum of the total weight, over a provably nonempty set (weight 1 on singletons), so no junk infimum. This is the LP relaxation of graph colouring exactly as in the literature.

The witness family is the join of t copies of C₅ on n = 5t vertices. The Lean proof of χ(G_t) ≥ 3t is genuine: any proper colouring uses ≥ 3 colours on each C₅ copy (proved by a short case analysis, `three_colors`), colour sets of different copies are disjoint (join adjacency), so 3t ≤ k. The proof of χ_f(G_t) ≤ 5t/2 is the classical half-weighting on the five distance-2 pairs per copy: each pair is independent in C₅, each vertex lies in exactly two distinct pairs ({a,a+2} and {a+3,a+3+2=a}), and there are ≤ 5t pairs — I checked each of these steps by hand, including the s₁ ≠ s₂ and Fin 5 arithmetic. Hence gap ≥ 3t − 5t/2 = t/2 = n/10, i.e. M(5t) ≥ n/10 = Θ(n), while n/(log n)² = o(n) (proved via (log n)² → ∞). The asymptotic composition (`maxGap_ge` along t ↦ 5t against an eventual bound with constant 1/20) is sound; since Fin n is finite the sup is a genuine maximum. Refuting the order clause refutes the conjunction.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hash of `conjecture.md` and of the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly).

## Verdict
APPROVED. A correct, faithfully formalized disproof of the order clause under all natural readings; builds, axioms, PDF, and source correspondence all verified independently.
