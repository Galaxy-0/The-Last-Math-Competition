# Solution Review — Conjecture 00000008975 (PR 566)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004203600`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture `conjectures/00000008975.md` read in full: the boundary K-matrix (reflection) equation is asserted to have polynomial solutions in `2^{rank G − rank H}` families **with order at most 2**. No SOURCE.md is present in the submission (absent, not failed).
- LaTeX: `report.tex` rebuilt from scratch with `latexmk -pdf` (clean compile, 2 pages). Text of the shipped `report.pdf` (built with Tectonic) compared against the rebuild via pypdf: identical after folding ligatures/spacing; only hyphenation-point artifacts (`matri-ces` vs `matrices`, `Math-lib` vs `Mathlib`) differ between engines. Content match confirmed.
- Lean: fresh `lake build` in a clean extraction with toolchain lean4 v4.19.0 and Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b` — **0 errors**; a single cosmetic linter warning (`tac1 <;> tac2` where `(tac1; tac2)` suffices, Main.lean:140).
- Axioms: `Main.lean` itself runs `#print axioms` on all twelve results, including `counterexample`; every one depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `axiom`, `unsafe`, `@[implemented_by]`, `extern`, or `admit` anywhere in the submission.
- Auxiliary code: none (README/VERIFICATION prose only).
- Repo metadata: conjecture is in the unsolved pool; this submission claims a disproof.

## Semantic audit
The conjecture states, as a definition, the boundary reflection (K-matrix) equation, and asserts its polynomial solutions have `2^{rank G − rank H}` families with order at most 2. The submission disproves the order clause by explicit instance. On `V = ℝ²` take the flip `P` (swap of tensor factors), used as a constant-in-the-spectral-parameter R-matrix, and `K(u) = diag(1, 1+u³)` with `K₁(u) = K(u)⊗I`, `K₂(u) = I⊗K(u)`.

The mathematics is correct and I re-verified it independently both by hand and numerically (explicit 4×4 and 8×8 matrices in numpy). `P² = I` so R is invertible for every parameter; `R₂₁(w) = PR(w)P = P`. Flip conjugation swaps tensor legs, `P K₁(u) P = K₂(u)`, so the reflection equation's two sides become `K₂(u)K₂(v)` and `K₂(v)K₂(u)`, equal because both are diagonal — hence the equation holds for **all** real `u, v`, not merely at isolated points. The flip's constant Yang–Baxter identity `P₁₂P₁₃P₂₃ = P₂₃P₁₃P₁₂` (both sides send `e_a⊗e_b⊗e_c ↦ e_c⊗e_b⊗e_a`) is proved in Lean on the genuine 8-dimensional space, so R is supplied with an actual YBE proof rather than assumed. The matrix polynomial `diag(1, X³+1)` has degree exactly 3 (`1+X³` is the maximal entry), `K(0) = I`, det `K(u) = 1+u³ = (u+1)(u²−u+1)` vanishes only at `u = −1`, the entry `1` makes it primitive (no nonunit common divisor), and `K(1) = diag(1,2)` is non-scalar — so no degeneracy (scalar-matrix, common-factor cancellation, singular normalization) is responsible for the degree violation. Degree 3 > 2 refutes the stated order bound.

The Lean formalization matches this faithfully: `ReflectionEquation u v` is the exact matrix equality `R*K1 u*R*K2 v = K2 v*R*K1 u*R` (the correct specialization of the spectral-parameter equation since `R(u−v) = R(u+v) = R` and `R₂₁ = R` for the constant flip, and this is stated explicitly in both report and code comment), proved for all `u v : ℝ`; `counterexample` conjoins the universal reflection equation with `K 0 = 1` and `(polynomialK 1 1).natDegree > 2`. The quantifier structure is exactly the negation of the official universal "order at most 2" claim: one polynomial solution of the boundary reflection equation with order exceeding two. The report is transparent that only the order clause is targeted and that the `G/H` family-count clause is left untouched, and that a classification restricted to a specified nonconstant spectral R-matrix would be a different statement — but the official bilingual text imposes no such restriction, so the literal reading is the ground truth. One entry of degree 3 forces the matrix order (max entry degree) to be 3, so using `(polynomialK 1 1).natDegree > 2` is a sound witness.

## Issues found
None blocking. (Minor: the report is compiled with Tectonic vs the reviewer's pdflatex, causing only hyphenation artifacts; the Lean file has one cosmetic `<;>` linter warning.)

## Verdict
APPROVED. The disproof is mathematically correct, independently re-verified numerically and by hand, formalized faithfully against the official bilingual statement, builds cleanly from a pristine extraction with only the three standard axioms, and the shipped PDF matches the LaTeX source. The counterexample satisfies every hypothesis the official text actually states (polynomial solution of the boundary K-matrix equation, with invertible YBE-satisfying R) and violates the stated conclusion (order at most 2).
