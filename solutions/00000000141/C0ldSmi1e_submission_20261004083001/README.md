# Disproof of conjecture 00000000141

The proposed asymptotic undercounts actual permutations. For every `n`, an explicit injection from permutations on `n` labels to fixed-point-free involutions on `2n` labels proves `N(2n) ≥ n!`. These involutions consist only of two-cycles, and two is prime.

For every positive constant `c`, the proposed expression

`g_c(k) = c · k^(−1/2) · exp(2√(k/log k))`

is eventually at most `c exp(k)`. Thus at even indices it is bounded by `c (exp 2)^n`, while `n!` eventually exceeds every fixed multiple of that geometric sequence. This contradicts the claimed ratio limit of one.

The exact English and Chinese [conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000000141.md) is copied in `conjecture.md`. Both versions count permutations of labelled elements, not conjugacy classes or partitions. The disproof negates the displayed asymptotic with the exact printed positive constant `(4π)^(−1/2) exp(−1/2)`. It does not need to interpret the subsequent capacity-integral assertion.

## What Lean proves

All declarations are in namespace `Conjecture141`.

| File | Role |
|---|---|
| `Conjecture141/Counting.lean` | Full cycle predicate, actual permutation-subtype cardinality, explicit cross-matching injection and factorial lower bound |
| `Conjecture141/Growth.lean` | Exact proposed expression and source constant, eventual exponential bound, factorial domination and limit contradiction |
| `Conjecture141.lean` | Connection to the actual count, Mathlib asymptotic-equivalence predicate and final negation |
| `Check.lean` | Nine definition printouts and all 19 theorem type/axiom audits |

These files are under `lean/`.

`PrimeCycles` uses `σ.partition.parts`, which includes fixed-point cycles of length one. `cycleType` alone omits fixed points, so it is not the definition of admissibility. `N` is the actual `Fintype.card` of all admissible permutations of `Fin n`.

The cross-matching map sends the left copy of `i` to the right copy of `σ i`, and the right copy of `j` to the left copy of `σ⁻¹ j`. Lean verifies it is a permutation, has no fixed points, squares to the identity, and is injective as a function of `σ`. Its explicit relabelling to `Fin (2*n)` preserves these facts. Every cycle length divides two and is at least two, hence is prime. The cardinality inequality then proves `factorial_le_count_even`.

`count_not_asymptotic` rules out the proposed asymptotic for every positive leading constant. The final `conjecture141_disproof` negates `ConjectureClaim`, which uses Mathlib's actual `Asymptotics.IsEquivalent` relation and the exact source constant. The quotient-limit connection uses proved eventual positivity. The even subsequence is cofinal, and all needed growth bounds hold eventually. No finite sample, assumed counting formula, or unproved correspondence substitutes for the original sequence.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all dependency revisions appear in `lean/lake-manifest.json`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture141/Counting.lean
lake env lean -DwarningAsError=true Conjecture141/Growth.lean
lake env lean -DwarningAsError=true Conjecture141.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache download is optional and only supplies compiled dependencies. If its executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`. The submission itself must still be built.

Reproduce the report with `tectonic main.tex`. `main.tex` and `main.pdf` give the complete mathematical proof and formal correspondence. `SEMANTIC_REVIEW.md` and `verification/` preserve independent internal review and local verification evidence. No numerical auxiliary program is used or needed. These checks are distinct from official maintainer acceptance.
