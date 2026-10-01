# Lean 4 verification for the disproof of conjecture 00000000499

Core Lean only (no Mathlib).  Zero axioms, zero `sorry`.

Toolchain: `leanprover/lean4:v4.33.1`

## Build and audit

```sh
lake build
lake env lean Check.lean
```

Expected: `C1_eq`, `C2_eq`, `C3_eq` and `attack` each report
`does not depend on any axioms`.

## What is proved

Two ordered simple random walks, starts `(x1, x2) = (0, 4)`, endpoints
`(y1, y2) = (1, 3)`, `w1(t) < w2(t)` at every time `t = 0..T`; all `4^T` joint step
sequences are equally likely.

- `C1 = 1`  of `4`  joint paths for `T = 1`  -> `p = 1/4`;
- `C2 = 0`  of `16` joint paths for `T = 2`  -> `p = 0` (parity);
- `C3 = 8`  of `64` joint paths for `T = 3`  -> `p = 1/8`;
- `attack` : `(C1 * 64) != (C3 * 4)`, i.e. `1/4 != 1/8`.

Since `p` takes two different values at the same endpoints, it cannot equal the
conjecture's `T`-free right-hand side (GUE ordered-eigenvalue joint density at the
endpoints times the Vandermonde factor `(y2-y1)-(x2-x1) = -2`) for all `T > 0`.

All coordinates are shifted by `+2` so every position is a `Nat` (walk 1 dips to
`-1` at worst, walk 2 to `+2` at worst); a constant shift preserves strict order
and the endpoint tests (endpoints become `3` and `5`), so the count is unchanged.
