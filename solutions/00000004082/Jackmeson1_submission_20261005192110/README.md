# Disprove conjecture 00000004082: the Kuramoto critical coupling is not c₁ times the mean absolute frequency deviation

- **Model.** All-to-all Kuramoto, θᵢ' = ωᵢ + (K/n) Σⱼ sin(θⱼ − θᵢ); `Locked ω K` (a phase-locked state exists) is proved equivalent to an ODE trajectory with constant phase differences (`locked_iff_phaseLockedSolution`).
- **Threshold.** K_c(ω) = sInf {K ≥ 0 | Locked ω K}, the conjecture's onset threshold; the formula's dispersion is (Σᵢ |ωᵢ − ω̄|)/n.
- **Necessary condition.** At any locked state Ω = ω̄ and |ωᵢ − ω̄| ≤ K (the antisymmetric double sine sum vanishes).
- **Witnesses.** For every n ≥ 6, two two-cluster vectors with mean 0 and mean absolute deviation 1 (for n = 6: (1,1,1,−1,−1,−1) and (3,−3/5,…,−3/5)). The first locks for all K ≥ n²/(6(n−3)) via explicit arcsin phases; the second cannot lock below K = n/2; since n²/(6(n−3)) < n/2, their K_c values differ.
- **Conclusion.** For each n ≥ 6, K_c is not any function of the mean absolute deviation; in particular no c₁ (even n-dependent) works. The same holds for the unnormalized coupling K Σⱼ sin, phase-cohesive locking (|θᵢ − θⱼ| < π/2), and the threshold inf {K | locked for all K' ≥ K}.
- **Scope.** Only the formula clause is refuted; the undefined phrase "dispersion spectrum" is not used. Context (retrieved arXiv abstracts): Dörfler–Bullo 1011.3878, Bronski–Carty–DeVille 2007.04343.
- **Main theorem.** `C4082.conjecture4082_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 346 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4082/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004082.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4082.conjecture4082_false`, `C4082.conjecture4082_false_universal`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004082 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
