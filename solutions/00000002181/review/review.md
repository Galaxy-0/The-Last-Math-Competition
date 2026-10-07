# Solution Review — Conjecture 00000002181 (PR 688)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005114833`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000002181.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; only glyph/ligature extraction artifacts.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `C2181.conjecture_2181_false`, `C2181.parity_violates`, and `C2181.no_log_bound` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` (3 lines, all clean) and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale `conjecture.md` and `Basic.lean` entries (files verified correct).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000002181/Jackmeson1_submission_20261005114833/`; no existing solution on `main`.

## Semantic audit

The first clause of the conjecture — `s(f) ≤ √2 · log n · ‖f̂‖₁` — is formalized as `FirstClause L enc` over the standard normalized Walsh Fourier conventions (characters `χ_S = ∏_{i∈S} sgn(x_i)`, coefficients `2^{−n}Σ g χ_S`, spectral norm `Σ_S |ĝ(S)|`), with the quantifier structure exactly as stated (∀ n ≥ 2, ∀ Boolean functions). The log base and output encoding are unspecified by the conjecture; the submission refutes the clause for the natural log and log₂, and for both the ±1 and 0/1 encodings, which removes all room for a convention-based escape.

The parity computations are complete and elementary-in-the-best-sense. Sensitivity: flipping any bit flips the parity (sign product picks up one `sgn(¬b) = −sgn(b)`), so `s(PAR, x) = n` at every input, giving maximum and average sensitivity `n`. Spectral norm: `Σ_x (−1)^{PAR(x)}χ_S(x)` factorizes over coordinates via `Σ_x ∏ h_i(x_i) = ∏ (h_i(true) + h_i(false))`, yielding `2⁲` exactly at `S = [n]` and 0 elsewhere, so `‖ĝ‖₁ = 1`; the 0/1 encoding is `(1 − sgn∘PAR)/2`, giving coefficients `½` at `∅` and `−½` at `[n]`, again norm 1. The inequality `√2 ln n < n` is proved via `ln n ≤ n/e` and `√2 < 3/2 < e` (and analogously for log₂ via `e ln 2 > √2`). Decisive instance: `n = 2`, `s = 2 > √2 ln 2 ≈ 0.980`.

Two strengthenings make the refutation airtight against any remaining convention choice: `no_log_bound` shows `C·ln n·‖f̂‖₁ < s(PAR_n)` for all large `n` for every constant `C` (covering every logarithm base, since `log_b n = ln n / ln b`), and the AND function (`weights 1`, threshold `n`) shows the same failure inside the class of linear threshold functions, with the ±1 spectral norm honestly bounded by 3 rather than overclaimed. I spot-verified the Fourier claims by hand (parity has a single Walsh coefficient; AND's 0/1 coefficient sum is `|χ_S(all-true)|/2ⁿ` summed to 1). The second conjunct ("pointer maxima of real hypercubical faces") is undefined in the text and unused — legitimate, since the conjunction already fails.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt`; actual files verified.
- No mathematical or semantic issues.

## Verdict

APPROVED. A decisive and convention-robust disproof with fully machine-checked Walsh analysis, clean build and axioms, and a report that maps onto the Lean development statement by statement.
