# Solution Review — Conjecture 00000004399 (PR 684)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005112810`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000004399.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization (11-character extraction delta); no content differences.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `Conjecture4399.conjecture4399_false` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has a stale `conjecture.md` entry (the shipped file matches the official conjecture byte-for-byte).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000004399/Jackmeson1_submission_20261005112810/`; no existing solution on `main`.

## Semantic audit

The conjecture is the conjunction of an existence clause (a non-complete non-bipartite common graph of order 6) and a minimality clause (6 is the least such order). The submission covers all three defensible readings of "common" — the standard asymptotic homomorphism-density notion (`t(H,G) + t(H,Ḡ) ≥ 2^{1−e(H)} − ε` for all large `G`), an asymptotic positive-bound reading, and the conjecture's own literal wording (some uniform positive lower bound over *all* graphs) — and refutes the conjecture under each. This is the right posture, since the definition sentence in the conjecture does not mention `2^{1−e(H)}`.

Under the standard reading the bowtie (vertices `0..4`, triangles `{0,1,2}`, `{0,3,4}`) is proved common: `hom(bowtie, G) = Σ_v T_G(v)²` via `bowtieEquiv` (a homomorphism is exactly a center image plus two ordered triangle-closing pairs; images of adjacent vertices are distinct since graphs are loopless, so no degenerate triangles); Goodman's bound is proved from scratch — the pointwise identity `2·mono + ang(x,y,z) + ang(y,x,z) + ang(z,x,y) = 2·dist3` (a non-monochromatic distinct triple has exactly two bichromatic angles — I re-verified all cases), summed to `2M + 3A = 2n(n−1)(n−2)` with `A = Σ_x 2d(x)d̄(x)` and `4dd̄ ≤ (n−1)²`, giving `M = ΣT_G + ΣT_Ḡ ≥ n(n−1)(n−5)/4`; then Cauchy–Schwarz (`S₁² + S₂² ≥ (S₁+S₂)²/2`, `(n−6)² − n(n−12) = 36`) yields `t + t ≥ 1/32 − 3/(8n)` for all `n ≥ 1` (trivial for `n < 12`). With `e(bowtie) = 6` and `2^{1−6} = 1/32`, taking `N > 3/(8ε)` proves `Common bowtie`; `b = 1/64` proves `CommonPos`. The bowtie is order 5, non-complete (`1 ≁ 3`), and non-bipartite (contains a triangle, decided directly), so the minimality clause fails — 5 < 6.

Under the literal uniform reading the submission shows the *existence* clause fails instead: any non-bipartite graph has an edge, and a graph with an edge has zero homomorphisms into the single-vertex graph `K₁` (an edge would map to a loop), where `t(H,K₁) + t(H,K̄₁) = 0` since `K̄₁ = K₁`; so no `b > 0` lower bound over all graphs exists and no non-bipartite graph of order 6 is "common". Either way the conjecture is false. The graphon-reading remark (`t(bowtie, W) = ∫τ² ≥ t(K₃,W)²` combined with Goodman's `t(K₃,W) + t(K₃,1−W) ≥ 1/4` giving `≥ 1/32`) is consistent, though flagged as not formalized. Density conventions (injective vs homomorphism density) differ by `O(1/n)` and cannot affect the asymptotic clauses, as the report notes.

## Issues found

- Minor hygiene: one stale `conjecture.md` entry in `verification/SHA256SUMS.txt`; the file itself is correct.
- The report does not decide existence under the standard reading (order-6 clause); it doesn't need to — minimality fails.

## Verdict

APPROVED. A complete, self-contained disproof (Goodman's bound proved in full rather than imported), valid under every reading of the ambiguous definition, with clean build and axioms and a report that matches the Lean development.
