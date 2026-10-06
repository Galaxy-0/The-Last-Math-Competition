# Disprove conjecture 00000000421: the expected number of addable cells is ≥ 7/3 at every prime size, so it does not tend to 2

- **Reading.** T is a uniformly random standard Young tableau with n cells; a(T) counts the addable (outer-corner) cells of its shape, i.e. cells x ∉ μ such that μ ∪ {x} is again a Mathlib `YoungDiagram`. The uniform measure on Young diagrams (`E_shape`) is covered too.
- **Corners.** Every nonempty diagram has the two addable cells (0, rowLen 0) and (colLen 0, 0); a non-rectangular diagram has a third, (k, rowLen k), where k is the first row shorter than row 0.
- **Primes.** A rectangle with a prime number p of cells is a single row or a single column, each carrying exactly one standard tableau; for p ≥ 3 the hook (p−1, 1) gives a tableau of another shape. Averaging gives E_SYT(p) ≥ 3 − 2/t_p ≥ 7/3 (t_p = number of tableaux), and likewise for E_shape.
- **Refutation.** Since there are infinitely many primes, E does not tend to 2; the weakest form of the rate clause, |E_n − 2| ≤ C/log n for all large n, fails as well.
- **Tableaux in Lean.** A standard tableau is an injective `pos : Fin n → ℕ×ℕ` whose image is a lower set, with entries increasing along rows and columns.
- **Not covered.** The Plancherel measure (the same counting works on paper), semistandard tableaux, and a "removable corners" reading. The fact that E_SYT → ∞ is a remark only (numerics to n = 22, OEIS A000085 retrieved).
- **Main theorem.** `C421.disproof`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 432 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture421/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000421.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C421.disproof`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000421 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
