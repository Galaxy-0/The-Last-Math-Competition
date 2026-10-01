# Lean verification of the disproof of conjecture 00000000405

Core Lean only (no Mathlib). Toolchain `leanprover/lean4:v4.33.1`.

```bash
lake build
lake env lean Check.lean
```

`Check.lean` audits every theorem with `#print axioms`; all print
`does not depend on any axioms` — zero axioms, zero `sorry`.

## What is verified

- `sytShape21 = 2`: `K_{(2,1),(1^3)}`, i.e. the number of standard Young tableaux of
  shape `(2,1)`, computed by brute force over all 64 fillings `a,b,c ∈ {0..3}` of the
  cells (0,0), (0,1), (1,0) with the standardness test
  (entries `1..3` distinct, `a < b` row, `a < c` column) — by `rfl`.
- `colHeights [2,1] = [2,1]`: the shape `(2,1)` is self-conjugate, hence
  `K_{(2,1)',(1^3)} = K_{(2,1),(1^3)} = 2` — by `rfl`.
- `Nat.factorial 3 / (3*1*1) = 2`: hook-length cross-check — by `rfl`.
- `Nat.factorial 3 % (2*2) = 2` and `≠ 0` (both as a `Nat` equation refuted by
  `Nat.succ_ne_zero` and as a `Bool` `== false` computation) — by `rfl`.
- `disproof_00000000405`: conjunction of all attack values, concretizing that for
  `n = 3`, `λ = (2,1)` the spin-pairing product `4` does not divide `3! = 6`.
