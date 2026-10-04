# Solution Review — Conjecture 00000000156 (PR 431)

**Submission:** GodBlf — `GodBlf_submission_20261004164810`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Read `conjectures/00000000156.md` in full. The official bilingual claim is that the probability that a uniformly random ±1 `n×n` matrix has prime determinant in absolute value is asymptotic to `c/n` for an explicit constant `c`. The report and Lean theorem formalize exactly this probability and refute exactly this asymptotic claim.
- **Repository structure.** PR head `70f2bf946fa6ca0985b44ec02aba078bcf02ab4c`, from clean base `4cc82278...`, adds only `solutions/00000000156/GodBlf_submission_20261004164810/`. The folder name and timestamp are valid. No metadata, conjecture, root, or unrelated files were changed. Base metadata marks the conjecture neither proven nor disproven and has no prior first solver.
- **LaTeX/PDF.** Read the complete LaTeX report and both pages of the shipped PDF. Rebuilt from a fresh copy with `pdflatex` twice; both passes exited 0, produced the same two-page content, and reported no LaTeX errors. Ghostscript rendered the shipped PDF successfully. The shipped PDF corresponds to `main.tex`.
- **Lean.** Rebuilt the full pinned Lean/Mathlib project independently in a fresh directory: `lake exe cache get` exit 0; `lake build` exit 0 (1822 jobs); `lake env lean Check.lean` exit 0; `lake update` exit 0 and did not alter the manifest. All five advertised theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, extra axiom, unsafe definition, `implemented_by`, `extern`, or `skipKernelTC`. No incomplete proof.
- **Auxiliary code.** None is needed: the proof is a general all-dimension Lean theorem, not a finite computation. Coverage was checked statement-by-statement and is universal rather than sample-based.

## Semantic audit

For every `n ≥ 3`, subtract row 0 from rows 1 and 2. Every changed entry is a difference of two signs, hence lies in `{-2,0,2}`. Writing the two changed rows as `2u` and `2v`, determinant row-addition invariance and two applications of homogeneity give `det A = 4 det C` with integer `C`. Thus `4 | det A`.

If `|det A|` were prime, then `2 | |det A|`; the only prime divisible by 2 is 2, but `4 ∤ 2`. Therefore `|det A|` is not prime for any sign matrix of dimension at least 3. The Lean theorem `four_dvd_det` proves this for every `n ≥ 3` and every sign matrix, and `no_prime_det` connects it to `Nat.Prime` on the actual determinant's `natAbs`.

The probability model is faithful: every Boolean matrix uniquely encodes one sign matrix and all Boolean matrices are counted uniformly. Consequently the favorable event is empty and `primeProbability n = 0` for every `n ≥ 3`. For every positive real `c`, the ratio `primeProbability n / (c/n)` is eventually identically zero, so it cannot converge to 1. The final theorem
