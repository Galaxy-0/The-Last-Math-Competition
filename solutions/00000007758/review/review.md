# Solution Review — Conjecture 00000007758 (PR 652)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005075611`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — under the hypothesis "no real fixed point with attracting interval (real Julia set totally disconnected)" the integer orbit should be finite, with counting refinements and an x²+1 density claim; `conjecture.md` is byte-identical to `conjectures/00000007758.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `C7758.conjecture_7758_false` uses only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: escape estimate, growth bounds, and the empty-real-Julia-set argument re-derived by hand.

## Semantic audit
The conjecture is an implication whose hypothesis has two conjoined forms ("no real fixed point with attracting interval"; parenthetically "the real Julia set is totally disconnected") and whose first conclusion is finiteness of integer orbits. The submission refutes the implication with the conjecture's own named witness, x²+1, and strengthens its position by assuming both hypothesis forms simultaneously.

The witness genuinely satisfies both hypothesis forms under any interpretation. First, f has no real fixed point at all (f(x) − x = (x−½)² + ¾ > 0), so "no real fixed point with attracting interval" holds whatever "attracting" means — the Lean statement is parametrized by an arbitrary predicate `Attracting : (ℝ→ℝ) → ℝ → Prop`, which is the right way to handle an undefined term: the hypothesis is satisfied for every choice, so no unfaithful specialization is possible. Second, the Julia set conventions are the standard ones (filled Julia set = points of ℂ with bounded orbit, Julia set = its frontier — sourced from the literature in the report), and Lean proves `realJulia f0 = ∅`: every real x has |f^[3](x)| ≥ 5 (I verified 1 ≤ x²+1, 2 ≤ (x²+1)²+1, 5 ≤ ((x²+1)²+1)²+1), the open escape neighbourhood {z : |f^[3](z)| > 2} is disjoint from the filled Julia set by the escape estimate |z| ≥ 2 ⟹ |z²+1| ≥ |z|+1 (equivalent to (|z|−2)(|z|+1) ≥ 0), so no real point is even in the closure; the real filled Julia set is also empty (real orbits grow by ≥ ¾ per iteration) and its frontier is empty. The empty set is totally disconnected, so the hypothesis holds; the conjecture states no nonemptiness requirement.

The conclusion fails genuinely: `intOrbit f0 a` is the range of all iterates on the actual integer polynomial, and f(y) − y − 1 = y(y−1) ≥ 0 for integers makes every orbit strictly increasing, hence infinite (`Set.infinite_range_of_injective`) and unbounded (n = max(B−a,0)+1 escapes any bound B). Refuting the first conjunct of the conclusion refutes the implication, so the counting clauses are not needed; the report also honestly separates the different Northcott-type statement (the set of integer preperiodic points is finite — true, and empty here) and does not claim to refute it.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hashes of `conjecture.md` and the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly with clean axioms).

## Verdict
APPROVED. A correct and faithfully formalized counterexample with a non-degenerate witness (the conjecture's own polynomial); all audited checks reproduce.
