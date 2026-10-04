# Solution Review — Conjecture 00000007152 (PR 394)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004040351`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The realizability of equality [in the Weyl inequalities] is a common eigenbasis, and the combination of the realization is the index permutation pair" (disproof submission).
- LaTeX: pdflatex twice, exit 0 both passes, 0 errors; shipped report.pdf is a genuine 1-page PDF matching report.tex content (title and sections verified by text extraction).
- Lean build: `lake build` exit 0, "Build completed successfully", no warnings; five `#print axioms` lines all [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over lean/Main.lean and lakefile.lean for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC — no hits.
- Auxiliary code: no scripts (none needed); VERIFICATION.md claims match my independent reproduction. Independent NumPy recomputation: eig(A)={0,1,3}, eig(B)={0,2,3}, eig(A+B)={0.382,2.618,6} ⇒ λmax(A)=3, λmax(B)=3, λmax(A+B)=6=3+3; e=(1,0,0) common top eigenvector ((A+B)e=6e); ABw=(0,1,0)≠BAw=0; A,B do not commute. All match the Lean-proven values.
## Semantic audit
Conjecture literal claim (EN): "The realizability of equality is a common eigenbasis, and the combination of the realization is the index permutation pair." (CN: 等号的可实现为共同特征基且现的组合为指标的排列对.) The natural literal reading: realizing equality in the Weyl additive eigenvalue bound is done through a common eigenbasis (an index-permutation pairing of the shared basis). The submission refutes this: equality in the top Weyl bound λmax(A+B) ≤ λmax(A)+λmax(B) is attained by matrices with NO common eigenbasis.

Lean encodings (namespace `WeylEqualityCounterexample`):
- `def Eigenvalue (M : Mat) (lambda : ℝ) : Prop := ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • v` and `def LargestEigenvalue (M : Mat) (lambda : ℝ) : Prop := Eigenvalue M lambda ∧ ∀ mu, Eigenvalue M mu → mu ≤ lambda` — faithful eigenvalue/largest-eigenvalue definitions via nonzero eigenvectors.
- `def CommonEigenbasis : Prop := ∃ (b : Basis (Fin 3) ℝ Vec) (alpha beta : Fin 3 → ℝ), (∀ i, A *ᵥ b i = alpha i • b i) ∧ (∀ i, B *ᵥ b i = beta i • b i)` — faithful "common eigenbasis" (a basis of simultaneous eigenvectors; orthogonality not required, which only makes the refutation stronger).

Key theorems: `theorem conjecture_7152_counterexample : A.transpose = A ∧ B.transpose = B ∧ LargestEigenvalue A 3 ∧ LargestEigenvalue B 3 ∧ LargestEigenvalue (A + B) (3 + 3) ∧ ¬ CommonEigenbasis`. Largest eigenvalues are NOT assumed from a table: `largest_from_bound` derives them from quadratic-form bounds (Q A v ≤ 3S v, Q B v ≤ 3S v, Q (A+B) v ≤ 6S v, proved by nlinarith with (v1−v2)² hints) plus the eigenvector witness e. `no_common_eigenbasis` quantifies over an arbitrary-index `Basis ι ℝ Vec` of simultaneous eigenvectors, derives LA∘LB = LB∘LA via `b.ext`, and contradicts it by evaluating at w=(0,0,1): ABw = (0,1,0) vs BAw = 0.

Mathematical validity: equality λmax(A+B) = λmax(A)+λmax(B) holds iff A,B share a common top eigenvector — the well-known correct characterization — and NOT iff a common eigenbasis exists. The example A=diag(3,1,0), B=[[3,0,0],[0,1,1],[0,1,1]] shares top eigenvector e but does not commute, so no common eigenbasis of any kind exists. Non-vacuous: both matrices are real symmetric (the natural Weyl setting), equality is genuinely attained, and the common-eigenbasis negation is proved for arbitrary basis index type.
## Issues found
Interpretive nuance (non-blocking, flagged): the conjecture's "equality" could conceivably mean simultaneous saturation of ALL Weyl inequalities (λ_{i+j−n}(A+B) = λ_i(A) + λ_j(B) for all pairs), for which a common eigenbasis IS necessary — under that stronger reading this example would not refute the claim. However, the literal bilingual statement ("等号的可实现为共同特征基") carries no "all inequalities simultaneously" restriction, and the report openly declares the exact equality being addressed (the largest-eigenvalue extremal bound). Under the repo precedent that the literal statement is authoritative, the disproof stands.
## Verdict rationale
The Lean project builds cleanly with only standard axioms, proves the largest eigenvalues from first principles rather than assumed data, and establishes a genuine, independently re-verified counterexample: top-Weyl-bound equality without a common eigenbasis (in fact without commutativity), refuting the literal claim that equality realizability requires a common eigenbasis. LaTeX, PDF, and verification evidence are all consistent. Approved, with the interpretive nuance flagged above for the record.

## Disposition
APPROVED — merged into main (PR 394). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
