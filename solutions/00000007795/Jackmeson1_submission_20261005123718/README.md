# Disprove conjecture 00000007795: the unit square has Lipschitz boundary and lattice error 2m+1 at integer dilations, not O(m^{1/3})

- **Claim refuted.** The first conjunct: every body with Lipschitz boundary has E(t) = |tP ∩ ℤⁿ| − tⁿ·vol(P) = O(t^{n−2+1/3}).
- **Witness.** P = [0,1]² ⊂ ℝ² (n = 2, exponent 1/3): compact and convex with nonempty interior.
- **Lipschitz boundary.** Proved with the local Lipschitz-graph definition (rotated frames allowed), using explicit corner charts with direction (±1,±1)/√2 and a 2-Lipschitz φ.
- **Lattice count.** For every integer m ≥ 1: |mP ∩ ℤ²| = (m+1)² and vol P = 1, so E(m) = 2m+1, which is not O(m^{1/3}). The clause fails for integer dilations and for real t → ∞, per body and hence uniformly over the class.
- **Scope.** The C², Hölder and "jump" clauses are not needed (the conjunction already fails). Only n = 2 is formalized; the cube argument for every n is on paper.
- **Main theorem.** `C7795.conjecture7795_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 297 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7795/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007795.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7795.conjecture7795_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007795 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
