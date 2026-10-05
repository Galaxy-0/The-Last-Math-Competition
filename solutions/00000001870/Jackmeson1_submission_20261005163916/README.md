# Disprove conjecture 00000001870: the third cumulant of Tr U under Haar measure on U(N) is exactly 0, not (2πi/3)/N

- **Claim refuted.** For U Haar-distributed on U(N), the third cumulant of Tr U decays as c₃/N with c₃ = 2πi/3 and exact exponent 1.
- **Argument.** −I ∈ U(N), so Haar measure is invariant under U ↦ −U, and Tr(−U) = −Tr U. Every odd moment of Tr U vanishes, so κ₃(N) = E[X³] − 3E[X²]E[X] + 2E[X]³ = 0 for every N.
- **Objects in Lean.** U(N) is `Matrix.unitaryGroup (Fin N) ℂ`, proved compact; the Haar probability measure is `haarMeasure ⊤`; the trace is `Matrix.trace`; cumulants are defined from integrals of moments, and every moment is shown to be integrable.
- **Generality.** The vanishing is proved for every left- or right-invariant measure, and covers the mixed cumulants κ(X,X,X̄) and κ(X,X̄,X̄), κ₃(Re Tr U), and any three ℝ-linear functionals of Tr U.
- **Statement.** ¬(κ₃ ~ c₃/N) and ¬(N·κ₃(N) → c₃); more generally κ₃ is not asymptotic to c·N^(−α) for any c ≠ 0 and real α.
- **Not covered.** Other statistics (|Tr U|², Tr U^j for even j, log det(1−U)) and the COE/CSE ensembles.
- **Main theorems.** `C1870.conjecture_1870_false`, `C1870.kappa3_not_equivalent`, `C1870.mixed_cumulants_eq_zero`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 202 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #234 by orionsheep ("Disproof of 00000001870: rotation symmetry forces kappa_3 = 0, not 2*pi*i/(3N)") was closed without merging. The reviewer accepted the mathematics but rejected the Lean as vacuous: "the capstone theorem is literally (0:Nat) = 0 := rfl and the 'zero moments' are substituted numeric literals; no unitary matrix, Haar measure, trace, or cumulant appears in Lean, and the entire (mathematically sound) rotation-symmetry argument is prose-only." This submission formalizes the actual objects and the symmetry argument. U(N) is Mathlib's `Matrix.unitaryGroup (Fin N) ℂ` with the subspace topology of the matrix space and its Borel sigma-algebra. Lean proves that U(N) is compact and defines the Haar probability measure `haarU N = haarMeasure ⊤`, then proves `IsHaarMeasure` and `IsProbabilityMeasure` for it. X = Tr U is `Matrix.trace`, and the third (joint) cumulant is defined from Bochner integrals of moments. Lean proves that for every left- or right-invariant measure on U(N) and every N, the joint third cumulant of any three ℝ-linear functionals of Tr U vanishes. This includes κ₃(Tr U), the mixed cumulants with conj(Tr U), and κ₃(Re Tr U). The proof uses invariance under U ↦ (-1)U = -U. Lean then proves that κ₃(N) is not asymptotic to c·N^(-α) for any c ≠ 0 and any real α, and in particular that κ₃(N) ≁ (2πi/3)/N and N·κ₃(N) does not tend to 2πi/3.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1870/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001870.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1870.conjecture_1870_false`, `C1870.kappa3_not_equivalent`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001870 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
