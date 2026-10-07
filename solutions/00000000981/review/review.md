# Solution Review — Conjecture 00000000981 (PR 676)

**Submission:** Jackmeson1 — `solutions/00000000981/Jackmeson1_submission_20261005103420`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in underscore/quote glyph-extraction artifacts (`eigenvectors_linearIndependent'` etc.). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_false`, `conjecture_false_clm`, `finite_eigenvalues_ge`, `not_ball_subset_closure_pointSpectrum`: all exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean.
- **Auxiliary code:** none shipped.
- **Semantic audit:** pass (see below).
- **Sources:** definitions match Mathlib and standard usage; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture is an existence claim: there is a compact operator T with σ_p(T) dense in the unit disk and every invariant subspace containing an eigenvector. The submission refutes the first conjunct alone, which suffices for the conjunction regardless of how the second is read.

The core is the classical finiteness theorem for compact-operator eigenvalues, formalized in full: for δ > 0, the set of eigenvalues with |μ| ≥ δ is finite. The proof is the standard Riesz-lemma scheme, and I verified every step: eigenvectors for distinct eigenvalues are linearly independent (Mathlib); the spans M_n form an increasing chain of closed T-invariant subspaces with (T − λ_n)(M_{n+1}) ⊆ M_n; Riesz lemma in M_{n+1} produces unit vectors y_n at distance ≥ 1/2 from M_n; for m < n the identity Ty_n − Ty_m = λ_n(y_n − z) with z ∈ M_n gives ‖Ty_n − Ty_m‖ ≥ δ/2, contradicting compactness (the unit-ball images have compact closure, so Ty_n has a Cauchy subsequence). Note λ_n ≠ 0 since |λ_n| ≥ δ, so the division is legitimate. Density in the open disk is then impossible: the finite set F = {σ_p ∩ {|·| ≥ 1/2}} cannot meet the open annulus around any point t ∈ (1/2, 1) ∖ F, yet an open neighbourhood of t would have to meet σ_p if D ⊆ closure σ_p. The closed-disk reading is handled as well.

Faithfulness: compactness is Mathlib's `IsCompactOperator` (some neighbourhood of 0 maps into a compact set), given for general complex normed spaces — no completeness smuggled in, and Banach/Hilbert are special cases; both the linear-map form and the bounded-operator `E →L[ℂ] E` form are stated. `pointSpectrum` is the honest set of eigenvalues; "dense in the unit disk" is formalized at its weakest as ball 0 1 ⊆ closure σ_p (density of σ_p ∩ D in D and closed-disk density both imply it, as noted). The invariant-subspace clause is formalized literally (nonzero closed invariant subspaces contain eigenvectors) and simply never used — which is the correct logical structure for refuting a conjunction. The "unit disk" is read as a disk rather than the unit circle, as both language versions say; the real-scalar reading is noted as out of scope (and could not help the conjecture anyway).

Sanity check: for a compact operator the spectrum accumulates only at 0, so σ_p ∩ {|·| ≥ 1/2} is indeed finite; e.g. diag(1/k) on ℓ² has σ_p = {1/k}, whose closure misses nothing of the disk only in the sense of accumulating AT 0 — never dense in |z| > 1/2 ✓.

## Issues found

- None. The disproof is the strongest possible form: the first conjunct is impossible on every complex normed space, in both operator categories.

## Verdict

APPROVED. Classical compact-operator spectral theory formalized end-to-end with faithful definitions and exact negations; build and independent axiom audit clean.
