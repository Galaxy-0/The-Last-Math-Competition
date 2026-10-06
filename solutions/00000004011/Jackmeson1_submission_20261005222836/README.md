# Disprove conjecture 00000004011: the linear RDE dY = Y dX with a Gaussian driver has lognormal, not Fernique-type Gaussian, solution tails

- **Reading.** "Growth constant of the vector fields" = K in |V(y)| ≤ K(1 + |y|), the linear-growth RDE class (Friz–Riedel, arXiv:1104.0577, retrieved, list linear-growth RDEs as a standard class). The bounded-vector-field reading (where Gaussian tails are known) is not addressed.
- **Witness.** V(y) = y (K = 1, 1-Lipschitz), Y₀ = 1, the smooth Gaussian driver X_t = tG on [0,1] with G ~ N(0,1); the driver has a Gaussian tail P(|G| > t) ≤ 2exp(−t²/2) (`driver_tail`).
- **Solution.** For a C¹ driver the RDE is the classical ODE Y' = V(Y)X' (Wikipedia "Rough path", universal limit theorem; not formalized); its unique solution is Y_t = exp(tG) (`exp_isRDESolution`, `isRDESolution_unique`), so Y₁ − Y₀ = e^G − 1 is shifted lognormal (consistent with Friz–Riedel's remark on log-normal tails of linear RDEs).
- **Refutation.** For every c > 0 and T there is t ≥ T with P(N(Y) > t) > 2exp(−t²/c), for any norm N dominating the increment (`tail_not_fernique`); hence no constant c works, whatever its dependence on K and the driver's tail parameters (`no_fernique_constant`, sup-norm version `no_fernique_constant_supNorm`); the hypotheses are satisfiable (`concrete_instance`).
- **Scope.** The driver is a smooth random path, not Brownian motion; only the sup norm is formalized (terminal value, p-variation and Hölder norms are argued in the text).
- **Main theorem.** `C4011.tail_not_fernique`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 281 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4011/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004011.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4011.tail_not_fernique`, `C4011.no_fernique_constant`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004011 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
