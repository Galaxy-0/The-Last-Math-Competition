# Solution Review — Conjecture 00000004011 (PR 775)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005222836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** RDE tail bound universal constant.

## Checklist results

- **Official conjecture.** `conjectures/00000004011.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture asserts a universal Fernique-type tail P(‖Y‖ > t) ≤ 2exp(−t²/c) with c depending only on the growth constant of the vector fields and the tail parameters of the driver. The submission refutes it at K = 1: the linear RDE dY = Y dX, Y₀ = 1 on [0,1] with the smooth Gaussian driver X_t = tG (G standard normal, so the driver's own tails are P(|G| > t) ≤ 2exp(−t²/2), proved via Mathlib's `HasSubgaussianMGF`). Existence and uniqueness of the solution are proved (integrating factor Y(t)e^{−tg} constant), so every solution path has increment Y₁ − Y₀ = e^G − 1 — shifted lognormal. For any path functional N dominating the increment on solution paths (sup norm, terminal value, p-variation and Hölder norms all qualify; the sup-norm domination is proved in Lean), and for every c > 0 and every T, there is t ≥ T with P(N(Y) > t) > 2exp(−t²/c): take u = 1 + 20c + max(T,0), t = e^u − 1; then {G > u} ⊆ {N(Y) > t}, P(G > u) ≥ φ(u+1) by the density integral over (u, u+1], and 2exp(−t²/c) < φ(u+1) because t² ≥ u⁴/4 and 5u²c < u⁴/4. Hence `no_fernique_constant`: no c works at all, a fortiori none computable from the growth constant and driver tail parameters.

The reading is faithful and, where the text underdetermines it, conservative in the right direction: 'growth constant' is read as the linear-growth constant K (the standard reading in the RDE integrability literature, with Friz–Riedel quoted), the RDE for a smooth driver is the classical ODE (justified by the rough-path universal limit theorem, quoted), and the report explicitly declares the bounded-vector-field reading out of scope rather than stretching. The quantifier structure is exactly the negation of the claim, in its strongest form: the failure is for a *fixed* equation with fixed driver tail parameters, so no universal c exists; both the all-t and the eventual versions fail. No measurability of N(Y) is tacitly assumed — the lower bound uses only monotonicity of the measure — and a concrete instance on (ℝ, N(0,1)) with G = id verifies every hypothesis.

I checked the key estimate by hand and numerically (c = 1, T = 0: u = 22, t = e²² − 1, 2exp(−t²) ≈ 0 against φ(23) ≈ 1.5·10^{−115}; the inequality 2√(2π)e^{−t²/c} < 6e^{−t²/c} < e^{3−t²/c} < e^{−(u+1)²/2} chains correctly). The conclusion is also the known truth: linear RDEs with Gaussian drivers have log-normal tails (Friz–Riedel Remark 7, quoted), so the conjecture contradicts the literature and the submission exhibits the mechanism precisely.

## Issues found

None material.

## Verdict

APPROVED. A decisive disproof: the linear-growth RDE dY = Y dX with a Gaussian driver has shifted-lognormal solution tails, violating 2exp(−t²/c) infinitely often for every c > 0, so no Fernique-type constant exists — neither per equation nor as a function of the growth constant and driver tail parameters.
