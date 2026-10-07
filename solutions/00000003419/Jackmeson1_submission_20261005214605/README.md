# Prove conjecture 00000003419: commute time equals 2 × (edge count) × effective resistance

- **Setting.** A finite connected simple graph G with m edges, the simple random walk, unit (one-ohm) edges. Known theorem (Chandra–Raghavan–Ruzzo–Smolensky–Tiwari, Computational Complexity 1996, retrieved Crossref record; first presented at STOC 1989), proved from scratch.
- **Hitting time.** H(x,b) = E_x[T_b] = Σ_{t≥0} P_x(T_b > t), with P_x(T_b > t) the path-probability sum over trajectories avoiding b; convergence is proved via a Dirichlet solution and the minimum principle.
- **Effective resistance.** R_eff(a,b) = v(a) − v(b) for a unit-current potential L v = e_a − e_b (L = Mathlib `lapMatrix`); existence and independence of the choice of v are proved (Wikipedia "Resistance distance", retrieved).
- **Key identity.** L h_b = deg − 2m·e_b for h_b = H(·, b), so (h_b − h_a)/(2m) is a unit potential — the difference-of-potentials (Green function) route named in the statement.
- **Main result.** H(a,b) + H(b,a) = 2m·R_eff(a,b) for every unit potential and for `effRes`; commute time and R_eff are symmetric.
- **Scope.** H(b,b) = 0 (T_b counts from time 0); weighted graphs and multigraphs are not covered; Green functions are not built as separate Lean objects; the stray word "Holant" is ignored.
- **Main theorem.** `C3419.commute_time_identity`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 315 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3419/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003419.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3419.commute_time_identity`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003419 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
