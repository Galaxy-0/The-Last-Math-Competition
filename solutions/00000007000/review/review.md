# Solution Review — Conjecture 00000007000 (PR 644)

**Submission:** Jackmeson1 — `solutions/00000007000/Jackmeson1_submission_20261005072621`
**Head:** `4abe6facf077cd3af437765efb862c4c6090a7a8`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000007000.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of the shipped and rebuilt PDFs matches modulo standard glyph/ligature/hyphenation extraction artifacts (`‖·‖`, `|·|` font mapping, `ff`/`fi` ligatures). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the Lean sources. `Axioms.lean` replays `#print axioms Submission00000007000.conjecture7000` → `[propext, Classical.choice, Quot.sound]` only, independently re-run in this review. Axiom check: pass.
- Auxiliary `verification/` material: `build.txt` (fresh full Mathlib build log) and `axioms.txt` agree with the independently reproduced results. SHA256SUMS has three stale entries (`conjecture.md`, `lean/Conjecture7000/Basic.lean`, `proof.tex`); each recorded hash matches the shipped file after CRLF→LF newline normalization, so this is a bookkeeping artifact, not a content change. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

The conjecture asks for two functions with identical box norms but different scattering spectra, the separation realized by an explicit permutation pair with the same norms but different phase. The Lean decisive theorem `conjecture7000` states exactly this existential: it exhibits `f, g : ZMod 4 × ZMod 4 → ℝ` and a permutation pair `σ = (1 2)`, `τ = (0 1)` with `σ ≠ 1`, `τ ≠ 1`, `g = permute σ τ f`, `boxNorm g = boxNorm f > 0`, `intensity f ≠ intensity g` as functions, explicit witnesses `intensity f (1,0) = 2` and `intensity g (1,0) = 0`, equal intensity `intensity f (0,1) = intensity g (0,1)`, and `phase f (0,1) ≠ phase g (0,1)`. Every clause of the bilingual statement has a corresponding conjunct; no hypothesis was strengthened and nothing was trivialized. Nontriviality is guaranteed by `0 < boxNorm f` (the box-norm sum is 4, so the norm is 4^{-1/4} > 0).

The reading is faithful to the standard notions. The Gowers box norm is the quartic average `‖f‖_□⁴ = E f(x,y)f(x,y')f(x',y)f(x',y')`; the general lemma `boxSum_eq_sq` writes it as a sum of squares (hence nonnegativity) and `boxNorm_permute` proves full permutation-pair invariance by reindexing the four-fold sum with `σ.prodCongr (σ.prodCongr (τ.prodCongr τ))` — this is the layer-1 invariance the conjecture's "same norms" clause requires. The scattering spectrum is the diffraction intensity `I_f(ξ) = |f̂(ξ)|²` of the discrete Fourier transform, the standard structure factor; the phase is the unit complex number `f̂(ξ)/|f̂(ξ)|`. The report's Scope section honestly excludes the wavelet scattering transform and scattering-matrix readings, which the conjecture does not invoke.

I rederived the arithmetic independently. `f` is the indicator of `{0,1} × {0}`; its box sum counts the 4 tuples `x,x' ∈ {0,1}, y = y' = 0`, so `‖f‖_□ = (4/256)^{1/4} > 0`. The permuted `g` is the indicator of `{0,2} × {1}` (verified by `decide` on all 16 points). `f̂(1,0) = 1 + i^{-1} = 1 - i`, intensity 2; `ĝ(1,0) = 1 + i^{-2} = 0`; `f̂(0,1) = 2` and `ĝ(0,1) = 2i^{-1} = -2i`, equal intensity 4 with phases 1 and −i. The identity `i^k = e^{2πik/4}` used for the character is itself proved (`exp_eq`). All Lean computations agree with these values.

Build hygiene: zero errors and zero warnings; the only axiom dependencies are `propext`, `Classical.choice`, `Quot.sound` (replayed, not taken from the shipped log). The shipped `SEMANTIC_REVIEW.md` flagged a wording imprecision in an explanatory remark about `τ = (0 1)`; the shipped `proof.tex` already carries the corrected, properly scoped remark, which is explanatory only and not part of the formalization.

## Issues found

- Minor: three entries of `verification/SHA256SUMS.txt` (`conjecture.md`, `lean/Conjecture7000/Basic.lean`, `proof.tex`) are stale — they hash CRLF newline variants of the shipped files (verified by re-hashing after newline normalization). Non-blocking hygiene issue; the packaged `conjecture.md` is byte-identical to the official source.

## Verdict

APPROVED. The main Lean theorem is a faithful, fully machine-checked realization of the conjecture's existential statement, with a genuinely explicit permutation-pair separation, correct arithmetic that I rederived independently, a clean build, a clean axiom profile, and a report that matches the code.
