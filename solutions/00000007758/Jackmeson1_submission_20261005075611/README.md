# Disprove conjecture 00000007758: every integer orbit of x^2+1 is infinite

The conjecture: if `f ∈ ℤ[x]` (deg ≥ 2) has no real fixed point with an attracting interval and its real Julia set is totally disconnected, then every integer orbit `a₀, f(a₀), …` is finite (plus counting clauses).
- **Witness.** `f = x² + 1`, which the conjecture itself names. `f(x) − x = (x − 1/2)² + 3/4 > 0`, so `f` has no real fixed point; the attracting hypothesis holds whatever "attracting" means.
- **Julia set.** With `J(f)` the boundary of the filled Julia set `{z ∈ ℂ : orbit bounded}`: for `|z| ≥ 2`, `|z²+1| ≥ |z| + 1`, and every real `x` has `f³(x) ≥ 5`, so a complex neighbourhood of `x` escapes. The real Julia set and the real filled Julia set are empty.
- **Orbits.** `f(a) ≥ a + 1` for every integer `a`, so every integer orbit (e.g. `0, 1, 2, 5, 26, 677, …`) is strictly increasing, infinite and unbounded.
- **Main theorem.** `C7758.conjecture_7758_false` takes an arbitrary predicate `Attracting` and refutes "deg ≥ 2 ∧ no attracting real fixed point ∧ real Julia set totally disconnected → every integer orbit finite".
- **Scope.** Not refuted: "the set of integers with finite orbit is finite" (a true Northcott-type statement). The counting clauses are not needed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 197 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7758/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007758.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7758.conjecture_7758_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007758 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
