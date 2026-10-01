# Lean verification for the disproof of TLMC 00000000602

Core Lean 4 only (no Mathlib). `Main.lean` encodes Gaussian-integer
arithmetic from scratch and machine-checks the counterexample:

- `Vtrefoil` is the Jones polynomial of the right-handed trefoil `3_1`,
  `V(t) = t + t^3 - t^4`, in the standard normalization `V(unknot) = 1`.
- `Vtrefoil_at_i` / `Vtrefoil_at_negi`: `V(±i) = -1`, so
  `|V(ω)|² = |V(i)|² = 1` for both primitive fourth roots `ω = ± i`.
- `det31 = 3`, so `det(3_1)² = 9`.
- `conjecture_identity_fails_31`: the conjectured quotient identity would
  force `9 = 1 · 1`, which is false.
- `counterexample_00000000602`: the packaged counterexample.

All proofs are pure kernel computations (`rfl`, `decide` on integer
literals); there is **no `sorry`** and, as the audit below shows,
**no axioms at all** (not even `propext`, `Quot.sound`, `Class.choice`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

Every `#print axioms` line must print `does not depend on any axioms`.

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
`lake-manifest.json` and `.lake/` are deliberately not committed
(see `.gitignore`); `lake build` regenerates them locally.
