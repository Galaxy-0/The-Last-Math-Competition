# Disproof of conjecture 00000000428

A Durfee square of side `d` contains `d²` boxes. A partition of `n` has only `n` boxes, so every Durfee size is at most `√n`. Consequently the actual uniform mean `Eₙ` is at most `√n`.

The conjecture instead proposes

```text
Eₙ = (√(6n)/π) log(√(6n)/π) + c + o(1).
```

Its leading term eventually exceeds `2√n`. The excess over the true mean therefore tends to positive infinity, excluding every fixed real constant `c` and additive remainder tending to zero.

## Scope and actual mathematical objects

The exact [bilingual conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/4cc82278ba1e5becc4d20b1e2a68dede094e2b8d/conjectures/00000000428.md) is included as `conjecture.md`. Both versions assert the displayed mean asymptotic. Durfee size means the side length of the largest square in the Ferrers diagram, as in [Pak–Panova, §2.1](https://www.math.ucla.edu/~pak/papers/Fixed12.pdf). All partitions of a fixed integer receive equal probability.

The proof uses Mathlib's actual `Nat.Partition n`, which retains repeated positive parts and requires their sum to equal `n`. It constructs the actual Ferrers `YoungDiagram` from column heights, proves that it has exactly `n` cells, and proves that it contains a `k × k` square exactly when `k ≤ durfee p`. The finite maximum defining `durfee` is proved to have no hidden cutoff restriction.

`partitionPMF n` is `PMF.uniformOfFintype (Nat.Partition n)`. The resulting `partitionMeasure` is a probability measure with equal singleton masses. `meanDurfee n` is the actual integral of the measurable, integrable Durfee statistic. Its finite arithmetic-mean formula and square-root upper bound are proved from this measure.

The final result is an infinite-limit disproof, not a finite numerical check. It excludes every real constant and the exact additive `o(1)` formulation. No replacement asymptotic or claim about a corrected distributional limit is needed.

## Lean project

All declarations use namespace `Conjecture428`.

| File under `lean/` | Role |
|---|---|
| `Conjecture428/Partitions.lean` | Actual partitions, unrestricted Durfee maximum, square-area bound, actual Ferrers diagram, square correspondence and exact area |
| `Conjecture428/Expectation.lean` | Actual uniform PMF and probability measure, singleton masses, integrability, integral mean and its upper bound |
| `Conjecture428/Asymptotics.lean` | Exact proposed leading term, divergence and exclusion of every finite additive correction |
| `Conjecture428.lean` | Exact additive asymptotic proposition and its negation for the actual uniform mean |
| `Check.lean` | All 13 definition/instance printouts and 38 type/transitive-axiom audits, covering 35 theorems and three instances |

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. The exact Mathlib revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins all nine dependencies. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture428/Partitions.lean
lake env lean -DwarningAsError=true Conjecture428/Expectation.lean
lake env lean -DwarningAsError=true Conjecture428/Asymptotics.lean
lake env lean -DwarningAsError=true Conjecture428.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache supplies compiled dependencies; the submission must still be built. If the cache executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`.

Run `tectonic main.tex` to reproduce the report. The package includes the matching PDF, exact source statement, independent internal semantic review and verification records. All mathematics is proved in Lean; no auxiliary numerical program is required. Local verification and internal review are separate from official maintainer acceptance.
