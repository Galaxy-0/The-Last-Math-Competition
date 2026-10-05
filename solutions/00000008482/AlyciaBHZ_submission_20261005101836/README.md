# TLMC 00000008482: refutation under both readings of bounded

The proposed universal `O(log n / n)` error bound fails for bounded local
costs, linear growth, and bounded successive increments, even when all three
restrictions are imposed together. Take the deterministic stationary family
`X(m,n) = sqrt(n-m)` for `m <= n`. It is subadditive, satisfies
`0 <= X(m,n) <= n-m`, has unit one-step costs, and has successive increments
of absolute value at most one. Its normalized expectations converge to
`gamma = 0`, also the infimum over positive lengths. The error is exactly
`1/sqrt(n)`, which is not `O(log n/n)` because `log n = o(sqrt(n))`.

The combined Lean theorem is

```lean
KingmanCounterexample.conjecture_00000008482_false_both_readings :
  ¬ UniversalUpperBound ∧ ¬ SharpnessClauseUniform
```

The original theorem `conjecture_00000008482_false : ¬ UniversalUpperBound`
and all existing declarations are retained. `UniversalUpperBound` uses the
actual limiting value, explicitly assumes convergence, and allows big-O
constants and thresholds to depend on the family. Failure therefore also
rules out constants uniform over families.

**Uniformly bounded reading:** `UniformlyBounded X` means
`∃ C : ℝ, ∀ m n, |X m n| ≤ C`. The new theorem
`uniformlyBounded_limit` proves both that `X 0 n / n` tends to zero and that
`gamma X = 0`; `uniformlyBounded_error_isLittleO` proves the error is
`o(log n/n)`. Both need only uniform boundedness. Analytically the error is
at most `C/n` for positive `n`, so the first upper-bound clause is true
under this reading, while logarithmic sharpness is false.

`UniformlyBoundedStationarySubadditive` contains exactly stationarity,
ordered subadditivity, and uniform boundedness. `SharpnessClauseUniform`
asserts that some such family has error that is **not** `o(log n/n)`.
`sharpness_false_uniform` refutes it. Thus the square-root family refutes
the first clause under the linear-growth / bounded-increment reading;
the uniform little-o theorem refutes the second clause under the uniformly
bounded reading. Either way the conjectured conjunction is false.

The constant-random-variable embedding on a one-point ergodic probability
space and the example attaining the `1/n` rate remain written proofs in
the report. We do not assert a disproof of the arbitrary-slowness clause
by itself.

Contents:

- `lean4/KingmanCounterexample.lean`: the complete Lean formalization.
- `lean4/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned project
  configuration for Lean and Mathlib v4.33.0.
- `report.tex`, `report.pdf`: self-contained mathematical proof, interpretations,
  and semantic audit.
- `verification.txt`: successful compiler output, axiom audit,
  and Python sanity-check output.
- `verify.py`: independent finite sanity checks using Python's standard library.

To build in a fresh environment:

```sh
cd lean4
lake exe cache get && lake build
cd ..
python3 verify.py
pdflatex report.tex
pdflatex report.tex
```

Lean compilation succeeded with Lean and Mathlib v4.33.0. The
Mathlib manifest pins revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
All nine audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
No external code is vendored.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).
