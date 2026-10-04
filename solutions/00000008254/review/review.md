# Solution Review — Conjecture 00000008254 (PR 418)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004055637`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the claim says every 2×2 game has an ESS; the zero game refutes it.
- Eligibility: base metadata is unsolved and the PR adds only its own properly named directory.
- LaTeX: independent build exit 0, two US Letter pages, no errors or box warnings; shipped and fresh PDF content matches.
- Lean: shared official pinned dependencies linked with the coordinator script; `lake build` exit 0 (`[2793/2794] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none in source.
- Auxiliary programs: none needed.

## Semantic audit

Take the symmetric 2×2 game whose payoff matrix is identically zero. The formal strategies are all nonnegative probability vectors on `Fin 2`, including pure boundary points, and expected payoff is the actual bilinear finite sum. It is provably zero for every pair of strategies.

For the direct ESS invasion definition, every resident `p` has a distinct feasible mutant. Given any alleged invasion radius δ, `ε=min(δ,1)/2` is positive, below δ, at most one, and produces a valid mixed population. But resident and mutant both earn exactly zero against that population, so the required strict resident advantage fails. The Lean proof establishes this for every resident and every possible limit. It also separately rules out the familiar Maynard Smith payoff criterion, whose two branches both require a strict inequality that cannot hold when all payoffs are zero. These are genuine definitions, not assumptions of nonexistence.

Since the official statement admits no nondegeneracy exception, this real symmetric two-strategy game falsifies the asserted completeness of 2×2 games and hence the compound conjecture.

## Verdict

APPROVED — the zero-game counterexample and its Lean proof correctly refute the universal 2×2 ESS-existence claim; all independent builds and PDF checks pass.
