# TLMC 00000000399: Calkin–Wilf digit golden law

**Proved under the binary-digit reading.** With root `1/1` at level zero and children `a/(a+b)` and `(a+b)/b`, the maximal reduced denominator at level `n` is `Nat.fib (n+2)`. Its binary digit count is both `(Nat.digits 2 (Nat.fib (n+2))).length` and `Nat.size (Nat.fib (n+2))`.

Writing `D(n)` for the maximal binary digit count and `φ = (1+√5)/2`, Lean proves

```
|D(n) - n * log₂ φ| ≤ log₂ φ + 1       (all n ≥ 0)
D(n) - n * log₂ φ = O(log n)          (n → ∞ in ℕ)
```

The proof keeps a sharp invariant on both coordinates and their sum. Mirror zigzag branches attain consecutive Fibonacci pairs. The Fibonacci recurrence and `φ² = φ+1` give `φ^n ≤ F_(n+2) ≤ φ^(n+1)`, and the digit-floor formula gives the bounded error. Positivity and coprimality ensure that the labels are actual fractions in lowest terms.

Lean also proves the law for every integer base `b ≥ 2`. Writing `D_b(n)` for the actual maximum of `(Nat.digits b denominator).length` over the level,

```
D_b(n) = Nat.log b (Nat.fib (n+2)) + 1
0 < D_b(n) - n * log_b φ ≤ log_b φ + 1       (all n ≥ 0)
```

Thus `D_b(n) = n * log_b φ + O(1)` with an explicit bound. For every `b ≥ 3`, Lean proves the linear lower bound

```
|D_b(n) - n * log₂ φ| ≥ n * (log₂ φ - log_b φ) - (log_b φ + 1),
```

unbounded error, and failure of `O(log n)` against the printed binary coefficient. The theorem `binary_coefficient_valid_iff` proves that, among integer digit bases at least two, the conjecture's asymptotic holds exactly when `b = 2`. Decimal digits therefore make the statement false. The convention of numbering the root as level one changes only the bounded error and is discussed in the report. The geometry clause is explanatory, and the proof exhibits its Fibonacci mechanism.

The level definition generates both children of every label; neither a bound nor a witness is built into it. Its finite-set representation may discard repeated labels without changing a maximum. The Fibonacci witnesses prove nonemptiness and attainment at every level. The logarithmic error is formalized as `Asymptotics.IsBigO Filter.atTop` on natural-number levels.

## Contents

- `lean4/GoldenLaw.lean`: complete formalization and eleven axiom audits, with original binary main theorem `CalkinWilf399.calkin_wilf_digit_golden_law`.
- `lean4/lean-toolchain`, `lean4/lakefile.toml`, `lean4/lake-manifest.json`: self-contained project configuration pinned to Lean and Mathlib `v4.33.0`.
- `report.tex`, `report.pdf`: full mathematical proof, interpretation, Lean correspondence, axiom audit, and references.
- `verification.txt`: recorded successful Lean compiler output, axiom audits, and independent Python output.
- `verify.py`: standard-library check of all nodes through level 17, agreement with Stern's sequence, and exact digit lengths and numerical error bounds for bases 2, 3, 4, 10, and 16 through level 10000.

## Build

In a normal Lean installation:

```sh
cd lean4
lake exe cache get && lake build
```

From the submission root:

```sh
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Lean compilation against the pinned Mathlib environment exited with code zero, with no warnings. Every audited theorem depends only on `[propext, Classical.choice, Quot.sound]`. No incomplete proof, new axiom, or kernel-bypass tactic is used. The finite and floating-point checks supplement the all-level Lean proof.

No trureturing code is vendored. The source uses Mathlib directly.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).
