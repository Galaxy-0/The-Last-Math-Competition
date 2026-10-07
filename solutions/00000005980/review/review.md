# Solution Review — Conjecture 00000005980 (PR 637)

**Submission:** Jackmeson1 — `solutions/00000005980/Jackmeson1_submission_20261005064511`
**Head:** `a556457562c6fff31f88b32dd4007b87a8a1540f`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000005980.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (word-boundary spacing around math, exponent glyphs). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms C5980.conjecture_5980` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; two SHA256SUMS entries (`conjecture.md`, `lean/Conjecture5980/Basic.lean`) hash CRLF newline variants — bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

The conjecture asks for two non-Hermitian models with the same singular spectrum but different eigenvector statistics, the separation realized by an explicit pair with the same spectrum but different polar decompositions. The decisive Lean theorem `conjecture_5980` realizes every clause through the `Separation` record: models `A` (fair on `{F 0, F 1}`) and `B` (fair on `{F ½, F −½}`) are probability laws (`PMF`) whose supports consist entirely of non-Hermitian matrices and which are non-Dirac; the pushforward laws of `singularValues` and even of `charpoly` coincide; the law of the eigenvector statistic differs (`½δ₁ + ½δ₀` vs `δ_{9/25}`); and the explicit pair `X = F 0`, `Y = F ½` lies in the respective supports with equal singular values, equal spectra, existing polar decompositions, every polar decomposition of `X` differing from every one of `Y` in both factors (uniqueness for invertible matrices, `det F(t) = −14`), and different statistic values `1 ≠ 9/25`. This is a faithful reading: in random matrix theory a "model" is a law on matrices, "same singular spectrum" is equality of the induced laws (here degenerate, i.e. the strongest form), and "eigenvector statistics" is a law of an intrinsic eigenvector-functional. The statistic `S(A) = ‖Π_{E₇(A)} e₀‖²` is sign-free and basis-covariant — a reasonable intrinsic choice, and the report is explicit that no universality is claimed.

I rederived the construction. `S₀ = [[7,12],[0,−2]]` has `χ = (X−7)(X+2)` and `S₀ᵀS₀ = [[49,84],[84,148]]` with trace 197, determinant 196, hence Gram eigenvalues 196 and 1 and singular values 14 and 1. `F(t) = R(t)S₀R(t)ᵀ` (rotation conjugation, tangent-half-angle parametrization `c = (1−t²)/(1+t²)`, `s = 2t/(1+t²)`) preserves the characteristic polynomial (a similarity) and the Gram spectrum (`FᵀF = R(S₀ᵀS₀)Rᵀ`); it is never Hermitian since `F₀₁ − F₁₀ = 12(c²+s²) = 12`. The eigenvalue-7 eigenvector is `(c, s)ᵀ` (because `Rᵀ(c,s) = e₀`, `S₀e₀ = 7e₀`), so the statistic is `c(t)²`: `c(0) = 1`, `c(1) = 0`, `c(±½) = 3/5` — giving the two different laws. The polar data `U₀ = (1/5)[[3,4],[4,−3]]` is orthogonal and `P₀ = (1/5)[[21,28],[28,54]]` is PSD (determinant 14 > 0, `21·P₀` = sum of two squares), with `U₀P₀ = S₀` checked entrywise; conjugation by `R(t)` gives the polar decomposition of each `F(t)`, and invertibility gives uniqueness via uniqueness of PSD square roots (`P² = AᵀA` determines `P`, then `U`). The `(0,0)` entries `3/5` vs the rotated value distinguish both factors. All of this matches the Lean development exactly.

Build hygiene: zero errors/warnings; axiom profile is the allowed minimum, replayed independently. The construction is credited as an adaptation of the accepted solution of the sibling conjecture 00000005960, with the singular-spectrum/polar layer new here.

## Issues found

- Minor: two entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md` and `lean/Conjecture5980/Basic.lean` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. A correct, fully machine-checked constructive proof: orthogonal conjugation produces a family of non-Hermitian matrices with constant singular values and spectrum but rotating eigenvectors, yielding two models whose eigenvector-statistic laws differ while every layer the conjecture calls "the same" coincides; the explicit pair has provably different (unique) polar decompositions in both factors.
