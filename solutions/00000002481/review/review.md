# Solution Review — Conjecture 00000002481 (PR 777)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005223759`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** PROOF. **Conjecture:** Durfee square partition geometry.

## Checklist results

- **Official conjecture.** `conjectures/00000002481.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors; eight benign linter warnings (unused binder names, unreachable `exact` hints), no errors or warnings affecting soundness.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture is the classical Durfee-square decomposition of partitions, and the submission proves all three of its natural components in full. (1) Decomposition: `durfeeEquiv d` is a genuine bijection between diagrams of Durfee side d and pairs (right piece with all cells in rows < d, i.e. ≤ d parts; lower piece with all cells in columns < d, i.e. parts ≤ d), with inverse `glue d d`, the cell-level splitting `durfee_decomposition`, and |λ| = d² + |α| + |β|. (2) Factorization: the generating function of Durfee-side-d diagrams is q^{d²}·C_d·C'_d with corner series C_d = C'_d = 1/(q;q)_d — built by the peel-the-first-column recursion C_{d+1} = C_d + q^{d+1}C_{d+1} and `gf_rowsLt_mul_prod` — and the total identity ∑_λ q^{|λ|} = ∑_d q^{d²}/(q;q)_d² holds as a `HasSum` in the coefficientwise topology (`hasSum_gf_durfee`), the count-level identity being proved by `card_nbij'` on the actual decomposition. (3) Symmetry: conjugation fixes the Durfee side, exchanges the two conjugated pieces (`durfeeEquiv_transpose`), and (glue_{r,s}(α,β))' = glue_{s,r}(β',α') (`glue_transpose`).

The definitions are faithful to the textbook: partitions are Mathlib `YoungDiagram`s; `durfee μ` is the least i with (i,i) ∉ μ, proved equivalent to both standard characterizations (largest contained square; largest s with at least s parts ≥ s); the empty partition and d = 0 are handled; '1/(q;q)_d' is stated as the multiplicative inverse against ∏_{i=1}^d (1 − q^i), which is exact in ℤ[[q]]; the summed identity is a coefficientwise HasSum, not a hand-wave. The submission states openly that the result is classical (Wikipedia's Durfee-square article is quoted) and that the contribution is the complete formalization — the correct posture for a true conjecture.

I verified the classical identity numerically (the coefficients of ∑_d q^{d²}/(q;q)_d² reproduce the partition numbers 1, 1, 2, 3, 5, 7, …) and spot-checked the peel bijection and the fiberwise count (durfee(λ)² ≤ |λ| bounds the sum over d). The build log contains only eight benign linter warnings (unused binder names, unreachable `exact` hints) and zero errors.

## Issues found

None material (eight benign unused-variable / unreachable-tactic linter warnings; zero errors).

## Verdict

APPROVED. The conjecture — the classical Durfee decomposition, its corner-piece generating-function factorization, and its conjugation symmetry — is proved exactly and completely, with faithful definitions and a clean build.
