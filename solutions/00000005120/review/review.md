# Solution Review — Conjecture 00000005120 (PR 641)

**Submission:** Jackmeson1 — `solutions/00000005120/Jackmeson1_submission_20261005071611`
**Head:** `b347dc80dfe0843881f7058fb561a77ddd418a5e`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000005120.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (Fréchet accent rendering, `ct` ligature, math-font mapping). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms Conjecture5120.conjecture_5120` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; three SHA256SUMS entries (`conjecture.md`, `lean/Conjecture5120/Basic.lean`, `proof.tex`) hash CRLF newline variants — bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

The conjecture asks for two matrices with the same spectrum but exponentially different matrix-function condition numbers, the separation realized by an explicit pair of Jordan structures. The decisive Lean theorem `conjecture_5120` matches this clause for clause, parametrized by the dimension `n ≥ 2` (the report explains, correctly, that "exponentially different" needs a growing parameter): `A n = (1/2)•1` (n blocks of size 1) and `B n = jordanBlock n (1/2)` (one block of size n) have equal characteristic polynomials `(X − 1/2)^n` and spectrum `{1/2}`; they are not similar (a scalar matrix is similar only to itself, so similarity would force the nonzero superdiagonal shift to vanish — `not_similar`); `cond(inv, A n) = 4` while `4^n ≤ cond(inv, B n)`, hence the absolute condition numbers differ by the exponential factor `4^{n−1}`; and the relative condition numbers are 1 vs at least `2^n/4`.

The reading is faithful to the standard notion of matrix-function condition number (Higham, *Functions of Matrices*, Ch. 3): the absolute condition number is the operator norm of the Fréchet derivative `L_f(X)`, here for `f(X) = X⁻¹` (Mathlib `Ring.inverse`, with `fderiv_inverse` giving `L(E) = −X⁻¹EX⁻¹`), in the ∞-operator norm (`Matrix.linftyOpNormedRing`). The report explicitly delimits scope: the exponential gap is claimed for this classical `f` and this norm, not universally (it even sketches why `f = exp` does not separate the same pair). The eigenvalue 1/2 is fixed and only the Jordan structure varies, which is exactly the conjecture's "explicit pair of Jordan structures".

I rederived the mathematics. `A n⁻¹ = 2I` gives `L(E) = −4E` with norm exactly 4 (upper bound by `‖4E‖ ≤ 4‖E‖`, lower bound from any nonzero `E`). The inverse of the Jordan block is explicit: `(J⁻¹)_{ij} = (−1)^{j−i} 2^{j−i+1}` for `i ≤ j` (`key`, `B_mul_Binv` check `B·B⁻¹ = I` entrywise: `½c(i,j) + c(i+1,j)` gives 1 on the diagonal and telescopes to 0 on the superdiagonal). Taking `E` = the matrix unit at `(n−1, 0)` with `‖E‖∞ = 1`, the `(0, n−1)` entry of `B⁻¹EB⁻¹` is `c(0,n−1)² = ((−1)^{n−1}2^n)² = 4^n`, and single entries are bounded by the operator norm, giving `4^n ≤ ‖L‖·‖E‖ ≤ ‖L‖`. Correct; these are the standard estimates, formalized without shortcuts. The relative-condition-number bounds use honest norm estimates (`‖B⁻¹‖ ≤ 2^{n+1} − 2` row sums, `‖B‖ ≥ 1/2`), not approximations.

Build hygiene: zero errors/warnings; the axiom profile is the allowed minimum, replayed independently. The report's `verbatim` rendering of the main theorem matches the actual Lean statement (I compared them term by term).

## Issues found

- Minor: three entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md`, `lean/Conjecture5120/Basic.lean` and `proof.tex` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. The classical Jordan-structure separation of the inversion condition number is correctly identified as the conjecture's content, fully formalized for every `n ≥ 2` with exponential gap `4^{n−1}`, with a clean build, clean axioms, and a precise, honest scope statement in the report.
