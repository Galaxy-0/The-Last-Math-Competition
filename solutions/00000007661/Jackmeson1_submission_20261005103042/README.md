# Disprove conjecture 00000007661: 1/(1−z)² is q-hypergeometric of radius 1, but its coefficient ratios converge to 1 only at rate 1/(n+1), not O(qⁿ)

For every complex q with 0 < |q| < 1:
- **The iff fails.** F₂ = 1/(1−z)² = Σ(n+1)zⁿ satisfies F₂(qz) = ((1−z)/(1−qz))² F₂(z) and has radius 1, but a_{n+1}/a_n − 1 = 1/(n+1) is not O(qⁿ).
- **The sharpness clause fails.** F₁ = 1/(1−z) is q-hypergeometric with radius 1 and has ratio exactly 1, so ratio − 1 = 0 = o(qⁿ), yet F₁ is not a polynomial. So does the variant with that clause inside the right side of the iff.
- **Definitions.** "q-hypergeometric type" (F(qz) = R(z)F(z) + S(z) with rational R, S) is formalized both analytically (on the open unit disk) and formally (in ℂ[[z]]); both versions are refuted. Radius of convergence is that of `FormalMultilinearSeries.ofScalars`; O/o are `IsBigO`/`IsLittleO` against qⁿ.
- **Main theorems.** `C7661.conjecture_false`, `C7661.conjecture_false_formal`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 250 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7661/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007661.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7661.conjecture_false`, `C7661.conjecture_false_formal`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007661 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
