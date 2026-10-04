# Counterexample to Conjecture 00000008178

The conjecture says that `(2, 3^10 * 109, 23^5)` is the smallest ABC hit,
where the minimum is measured by `c = a + b`. The smaller triple
`(3, 125, 128)` is positive and pairwise coprime, with radical
`rad(3 * 125 * 128) = 30 < 128`. It also satisfies the stated power-cutoff
type of condition at epsilon `1/4`: `30^4 < 128^3` implies
`30 <= 128^(1 - 1/4)` over the real numbers.

This disproves the minimum assertion and hence the conjunctive conjecture.
No claim is made about the separate asymptotic density or optimal algorithm
assertions. The witness has every entry greater than one.

## Contents

- `report.tex` and `report.pdf`: complete mathematical argument and scope.
- `lean/`: Lean 4.19.0 project with a pinned Mathlib dependency.
- `VERIFICATION.md`: commands, results, and final theorem axiom audit.

## Reproduce

With Lean installed through elan:

```sh
cd lean
lake exe cache get
lake build
lake env lean Main.lean
```

The manifest pins all dependency revisions. No local cache or compiled
Lean product is part of the submission. On Windows, use a sufficiently
short checkout path (or a temporary `subst` drive) to avoid path-length
failures when accessing Mathlib imports.

To compile the report with Tectonic:

```sh
tectonic -X compile report.tex
```

`ABC8178.counterexample` is the final formal theorem. The Lean definitions
use actual prime divisor sets, actual natural-number coprimality, and
Mathlib real exponentiation. There are no auxiliary computational scripts.
