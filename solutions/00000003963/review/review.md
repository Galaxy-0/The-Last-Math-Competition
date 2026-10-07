# Solution Review — Conjecture 00000003963 (PR 680)

**Submission:** Jackmeson1 — `solutions/00000003963/Jackmeson1_submission_20261005111725`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text extraction of shipped vs. rebuilt PDFs differs only in cosmetic glyph-extraction artifacts (√, ⊆, subscript `_`, soft hyphens). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_3963_false`, `algConn_johnson_ge`, `johnson_quad`, `normConn_johnson_ge`, `induced_not_bigOmega`: all exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean (no `sorry`/`native_decide`/`axiom`/`set_option`/`unsafe`/extern tricks).
- **Auxiliary code:** none shipped.
- **Semantic audit:** pass (see below).
- **Sources:** the Wikipedia quotations (Johnson graph adjacency, Fiedler value definition) match the cited pages; the PR adds only its folder; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture states that the algebraic connectivity of the layer graph ("the induced graph of a layer, a Johnson graph") attains its minimum over all layers at ℓ = n/2, of order Θ(log n / n²). The text is internally ambiguous — the subgraph of Q_n induced on a single weight-ℓ layer has no edges (two distinct weight-ℓ sets differ in ≥ 2 coordinates each way), so it is not a Johnson graph — and the submission correctly handles all three readings: (J) the Johnson graph J(n,ℓ) with the combinatorial Laplacian, (N) J(n,ℓ) with the normalized Laplacian, (I) the literal induced subgraph.

Under (J) the submission proves λ₂(L(J(n,k))) ≥ n for every n and every 1 ≤ k ≤ n−1. I verified the argument in detail: with the up/down operators D (sum over supersets adding one element) and U (sum over deletions), one has U Df = |A|f + Xf, D Uf = (n−|A|)f + Xf, U and D adjoint between consecutive levels; the key inequality ‖Df‖² ≤ m(n−m−1)‖f‖² for mean-zero f on level m+1 is proved by induction on m using Cauchy–Schwarz (Z² ≤ F·‖Uz‖² with ‖Uz‖² ≤ (m+1)(n−m−2)Z by the induction hypothesis) — the arithmetic (m+1)(n−m) − m(n−m−1) = n is exactly right. The variational lemma (every eigenvalue is 0 or ≥ c, and at most one is 0, by a two-eigenvector argument) converts the quadratic-form bound to λ₂ ≥ n. Since n is not O(log n/n²) along even n (Lean: `exists_large`, log n < 2√n), both the minimum-over-layers and middle-layer readings of the order clause fail. Under (N), λ₂(ℒ) ≥ n/(k(n−k)) = 4/n at k = n/2, likewise not O(log n/n²). Under (I), λ₂ ≡ 0, which is not Ω(log n/n²). Any reading of "of order Θ(log n/n²)" as a conjunction fails on its upper or lower half.

The scope statement is honest: under (J) all non-trivial layers have λ₂ = n (the remark gives the eigenvector x_A = [0∈A] − k/n), so the location clause "minimum at ℓ = n/2" is true (non-uniquely) and is not claimed as refuted; the conjecture falls through its order clause, which suffices for a conjunction. λ₂ is Mathlib's `eigenvalues₀` at index card−2 — the second-smallest eigenvalue with multiplicity, i.e. the Fiedler value quoted in the conjecture's definition.

Sanity check: J(4,2) (octahedral graph) has Laplacian spectrum {0, 4, 4, 4, 6, 6}, so λ₂ = 4 = n ✓; the conjectured Θ(log n/n²) is off by a factor n³.

## Issues found

- Minor: `lambda2` is defined as 0 when the vertex set has fewer than two elements (layers 0 and n); these degenerate layers are excluded from the minimum, which matches the conjecture's intent.
- The disproved Θ-clause is read along even n (ℓ = n/2 must be integral) — the natural reading.

## Verdict

APPROVED. All reasonable readings of the conjecture's order clause are refuted by Lean-proved spectral lower bounds with faithful definitions of every object (hypercube, layer, Johnson graph, Laplacian, Fiedler value, normalized Laplacian); the build, axiom audit, and PDF rebuild are all clean.
