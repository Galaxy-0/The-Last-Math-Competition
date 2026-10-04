# Solution Review — Conjecture 00000007177 (PR 398)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004041921`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The scaling of generalized eigenvalues is the quotient of the two spectra, and the extremum of the quotient is the definite pair" (definite-pair pencil spectral quotient); CN: 束谱的联合：广义特征值的刻度为两谱的商且商的极值为定度对.
- LaTeX: recompiled with pdflatex (twice) in /tmp/tlmc-review5/scratch/pr-398, exit 0, 1 page; shipped report.pdf is a real PDF (27195 bytes) whose extracted text matches report.tex content.
- Lean build: `lake build` exit 0 (1103 jobs); only output = 7 info lines from `#print axioms`, all `[propext, Classical.choice, Quot.sound]`; zero warnings.
- Forbidden content: grep for sorry/admit/native_decide/axiom decl/unsafe/implemented_by/extern/skipKernelTC over the submission's own .lean files: no hits. Only source file is Main.lean; lakefile pins mathlib c44e0c8e, Lean 4.19.0 (matches env).
- Auxiliary code: none shipped (no verify scripts); math independently re-derived with python3/numpy: Av = Bv = (1,-2) so λ=1 is a genuine pencil eigenvalue; eig(A) = {1,2}; eig(B) = {(5±√5)/2} ≈ {1.382, 3.618}; all four quotients α/β ≈ {0.724, 0.276, 1.447, 0.553} ≠ 1; both matrices symmetric positive definite. Matches README/report claims exactly.
## Semantic audit
Literal claim (EN): "The scaling of generalized eigenvalues is the quotient of the two spectra" — CN "广义特征值的刻度为两谱的商". The submission takes the reading that each pencil eigenvalue of (A,B) equals α/β for individual eigenvalues α of A, β of B, and refutes exactly that. Lean encodes the objects faithfully per standard definitions:
- `def Eigenvalue (M : Mat) (lambda : ℝ) : Prop := ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • v` — ordinary eigenvalue via nonzero eigenvector equation.
- `def GeneralizedEigenvalue (M N : Mat) (lambda : ℝ) : Prop := ∃ v : Vec, v ≠ 0 ∧ M *ᵥ v = lambda • (N *ᵥ v)` — pencil A − λB eigenvalue, standard.
- `def PositiveDefinite (M : Mat) : Prop := ∀ v : Vec, v ≠ 0 → 0 < dotProduct v (M *ᵥ v)` — quadratic-form definiteness, standard.
Final theorem:
`theorem conjecture_7177_counterexample : A.transpose = A ∧ B.transpose = B ∧ PositiveDefinite A ∧ PositiveDefinite B ∧ GeneralizedEigenvalue A B 1 ∧ ¬ (∃ alpha beta : ℝ, Eigenvalue A alpha ∧ Eigenvalue B beta ∧ beta ≠ 0 ∧ (1 : ℝ) = alpha / beta)`
Hypotheses of the definite-pair setting are not assumed but *proved* (A_symmetric, B_symmetric, A_positive, B_positive), so the counterexample lives inside the conjecture's scope — not an out-of-scope degenerate example. Supporting lemmas prove the full two-sided spectrum of A (A_spectrum_iff), the exclusion of 1 and 2 from B's spectrum via explicit coordinate equations, and `no_individual_spectral_quotient`: since 1 = α/β forces α = β, a quotient equal to 1 would need a shared eigenvalue, which is excluded. This contradicts the literal first clause of the conjecture (conjunction refuted); the second ("extremum … definite pair") clause is dispensable for a disproof of the conjunction, and the README/report say so explicitly. The report also carefully distinguishes the *true* variational statement (generalized Rayleigh quotient R(v) = vᵀAv/vᵀBv = 3/3 = 1 here) that is NOT disputed — this is exactly the right scope discipline, since the false reading is "quotient of the two spectra" (individual eigenvalues), not "quotient of the two quadratic forms". Not vacuous: all conjuncts are positive assertions proved, plus a negative universality statement. No numeric-facts-only shortcut: every step (positivity, spectrum, exclusion) is a real Lean proof; axioms are only the three standard Mathlib ones.
## Issues found
none blocking
## Verdict rationale
The submission faithfully encodes the conjecture's objects (matrix pencil, generalized eigenvalue, definite pair, individual spectra) in standard form, proves all hypotheses rather than assuming them, and exhibits a fully verified SPD pair whose pencil eigenvalue 1 is provably not any quotient of individual spectral values — directly contradicting the literal bilingual statement "the scaling of generalized eigenvalues is the quotient of the two spectra". Build is clean with only standard axioms, the PDF matches the source, and my independent numpy computation confirms every claimed matrix fact. The counterexample is robust (generic SPD pairs behave this way), not a degenerate edge case.

## Disposition
APPROVED — merged into main (PR 398). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
