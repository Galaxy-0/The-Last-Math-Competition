# Solution Review — Conjecture 00000002853 (PR 783)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006001755`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** cactus separation minimal degree.

## Checklist results

- **Official conjecture.** `conjectures/00000002853.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The crisp content of the conjecture is 'the minimal degree where cactus rank falls below rank is 5'. The submission formalizes this as `IsLeast separatingDegrees 5` over the set of positive degrees d admitting a nonzero complex form of degree d with cactus rank < Waring rank, and refutes it with the classical binary cubic F = x₀²x₁: the double point (y₁²) at [1:0] is apolar to F and has length 2 (homogeneous, saturated, Hilbert function ≡ 2 for t ≥ 1 via the standard-monomial count), so `cactusRank F ≤ 2` — under both the differentiation and contraction apolarity conventions — while `waringRank 3 F = 3` exactly (upper bound by the explicit decomposition 6x²y = (x+y)³ − (x−y)³ − 2y³ with 6^{-1/3}, 2^{1/3} scalings; lower bound by dehomogenizing a hypothetical ≤2-cube decomposition and killing the resulting linear system in t = 0, 1, −1, 2). Hence 3 ∈ separatingDegrees, ¬IsLeast separatingDegrees 5, and sInf ≤ 3.

The definitions are faithful to the apolarity literature (Bernardi–Ranestad / Bernardi–Taufer are quoted): zero-dimensional subscheme of length r as saturated homogeneous ideal with Hilbert function eventually constant r; cactus rank as the least apolar length; Waring rank as the least number of d-th powers of linear forms; both infima in ℕ∪{∞}. The restriction to positive degrees is justified and harmless (the witness has degree 3). The negation structure is exactly right: an existential-minimality claim ('the minimal degree is 5') is refuted by a concrete witness of separation at degree 3, and the vague second conjunct ('multi-point splitting constraint') carries no formal content, so the conjunction fails with the first. The true minimal separating degree is in fact 3 (quadratics do not separate), so 'is 5' is not merely unproven but false.

I verified by hand: ∂₁²(x²y) = 0 so (y₁²) ⊆ F^⊥; dim_C k[y₀,y₁]/(y₁²) at degree t ≥ 1 is 2; and the 4-point linear-combination identity in `not_two_cubes` indeed forces β₁³ = β₂³ = 0 and then 0 = 1. The Hilbert-function machinery is credited to the accepted 00000000539 package, and the reuse is legitimate and acknowledged.

## Issues found

None material.

## Verdict

APPROVED. A decisive, fully machine-checked disproof of the 'minimal degree is 5' clause by the classical degree-3 example x₀²x₁ (cactus rank ≤ 2 < 3 = Waring rank), with faithful definitions and correct quantifier structure.
