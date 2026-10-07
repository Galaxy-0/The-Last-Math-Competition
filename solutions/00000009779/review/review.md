# Solution Review — Conjecture 00000009779 (PR 779)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005230135`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** kernel regularity-decay optimal constant.

## Checklist results

- **Official conjecture.** `conjectures/00000009779.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The first clause of the conjecture — C^k kernels satisfy |λₙ| ≤ C n^{−k−1−d/2} — is refuted for every dimension D ≥ 1 and every k ≥ 0 by the Fourier kernel K(x,y) = f_s(x₀ − y₀) on [0,1]^D, with f_s(t) = ∑_{m≥1} m^{−s} cos(2πmt) and s = k + 5/4. The submission proves in Lean: f_s is C^k (termwise differentiation with the summable (2π)^i(j+1)^{i−s} bounds, since s − i > 1 for i ≤ k) and K is C^k on all of ℝ^D×ℝ^D; the exponentials e^{2πi(j+1)x₀} are continuous orthonormal eigenfunctions of the integral operator with eigenvalues exactly (1/2)(j+1)^{−s} (dominated convergence for the termwise integral against ∫₀¹ e^{2πipy} dy = δ_{p0}); K is symmetric and positive semidefinite (cos(u−v) = cos u cos v + sin u sin v); and the first n eigenvalues are ≥ (1/2)n^{−s}, which beats C·n^{−k−1−D/2} for large n because D/2 − 1/4 ≥ 1/4 > 0. Hence `EigenBound` fails for every C.

The formalization is careful about the one genuine gap between the conjecture's wording ('|λₙ|' for the nth eigenvalue) and a first-order formalization: `EigenBound K k C` — every n orthonormal eigenfunctions contain one of modulus ≤ C·n^{−(k+1+D/2)} — is a necessary consequence of the ordered-eigenvalue bound (n eigenfunctions all exceeding the bound would force |λₙ| above it), so its negation is stronger and refutes the literal claim a fortiori; the report states and proves this elementary bridge, though it is the one step not machine-checked. The counterexample also kills the two 'optimal constant' clauses, which presuppose that a working C exists, and the D = 1 case is radial (f_s even), so the radial clause fails as well.

I verified numerically that (1/2)n^{−k−5/4} > C·n^{−k−1−D/2} for large n whenever D ≥ 1 (it is equivalent to n^{D/2−1/4} > 2C) and that the coefficient series ∑ m^{i−s} converges exactly for i ≤ k, matching the C^k-but-not-C^{k+1} character of f_s. The growth lemma (choose n with n^{1/4} > 2C; factor n^{−(k+1+D/2)} = n^{−s}/n^{D/2−1/4}) is exact and machine-checked.

## Issues found

Minor: the bridge from ¬`EigenBound` to the ordered-eigenvalue formulation is argued in the report rather than formalized; it is elementary (multiplicity ≥ orthonormal count) and the direction is conservative. No fix required.

## Verdict

APPROVED. A decisive disproof of the decay clause for every dimension and every k by an explicit C^k, symmetric, positive semidefinite kernel whose leading eigenvalues decay strictly slower than any allowed ceiling, refuting the first clause and, with it, the whole conjecture including its radial reading.
