# Disprove conjecture 00000005402: the Möbius conversion of periodic-orbit counts has no μ(d)·d coefficients

- **Claim refuted.** Clause (i): the low-order conversion from total to primitive periodic counts is B_n = Σ_{d|n} μ(d)·d·T_{n/d}. Refuting it at order 2 makes the conjunction false.
- **Readings.** Six explicit readings of (total T, primitive B): T = periodic points / orbits of length dividing n / cumulative counts; B = primitive orbits or points of least period n.
- **Witness.** The permutation (0)(1)(2 3) of Fin 4: the formula predicts 0, 0, −1 where the true values are 1, 2, 1.
- **Coefficients forced.** From the identity on Unit and the swap on Bool, no integer order-2 conversion exists for (points, orbits), and for the other readings the coefficients are forced to be (1, −1) = (μ(1), μ(2)), so μ(2)·2 = −2 fits in neither slot.
- **Scope.** Clauses (ii) and (iii) are not needed; a repetition-weighted total T_n = Σ_{k|n}(n/k)B_k, which the text does not mention and which would make μ(d)·d correct, is not treated.
- **Main theorem.** `C5402.conjecture_5402_false` (Mathlib `minimalPeriod` / `periodicOrbit`).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 281 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5402/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005402.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C5402.conjecture_5402_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000005402 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
