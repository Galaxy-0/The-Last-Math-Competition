# Disproof of conjecture 00000000374 under three standard arithmetic heights

At the included endpoint `tau = 3`, the real number `0` has only finitely many distinct algebraic approximants of degree at most two satisfying the conjecture's strict error bound. Therefore its assertion `P(tau) = R` for every `tau <= 3` is false.

The original does not define `H`. This submission treats **naive coefficient height, Mahler measure, and absolute multiplicative Weil height separately**, with both real and complex approximants. It preserves the literal exponent and constant one. It does not claim a theorem for arbitrary height functions, logarithmic heights, archimedean house, or rescaled conventions. The separate Hausdorff-dimension assertions are not determined here.

`report.tex` and its matching three-page `report.pdf` contain the proof and scope. `ORIGINAL.md` is the exact bilingual statement. The formal project uses Lean 4.19.0 and Mathlib v4.19.0 at the exact revisions in `lean/lake-manifest.json`.

## Formal result

`TLMC374.source_conjunct_false` proves

```lean
¬ (∀ τ : ℝ, τ ≤ 3 → P d c τ = Set.univ)
```

for every `ApproximationDomain` (`real`, `complex`) and `HeightConvention` (`naive`, `mahler`, `absoluteWeil`). Its witness theorem is `TLMC374.zero_not_mem_P_three`.

`Counterexample.lean` defines the actual approximation sets and constructs the primitive integer minimal polynomial, including its degree, irreducibility, uniqueness up to sign, positive normalization, and all three height identifications. `HeightRoots.lean` proves the Mahler root-product bound and the actual-degree Weil-height identity. Infinitude counts distinct numbers; no irrational-target restriction or repeated-sequence surrogate is used.

## Reproduce

With the pinned Lean toolchain available, obtain the pinned dependencies and build:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true HeightRoots.lean
lake env lean -DwarningAsError=true Counterexample.lean
lake env lean -DwarningAsError=true Inspect.lean
```

The portable verifier uses Python's standard library and an existing cache of the nine pinned standard dependencies. It creates a new project, records commands and outputs, checks dependency revisions and tracked cleanliness before and after, and compares the complete compiled declaration inventory with the reviewed baseline. It does not download dependencies or overwrite this submission.

```sh
python3 verify.py --lake /path/to/lean-4.19.0/bin/lake \
  --dependency-root /path/to/pinned/packages --output /new/verification-results
python3 test_verify.py --compiled-controls \
  --lake /path/to/lean-4.19.0/bin/lake \
  --dependency-root /path/to/pinned/packages --output /new/control-results
```

Each `--output` path must be new. The negative controls intentionally compile invalid test fixtures outside the submitted project; their expected rejection is the successful test outcome. They are not proof assumptions.

The report uses ordinary LaTeX packages and can be rebuilt from `report.tex`. No numerical search or external mathematical computation is needed for the proof. See `VERIFICATION.md` and `verification/` for the actual local evidence and its limits. Local verification is separate from maintainer review and acceptance.
