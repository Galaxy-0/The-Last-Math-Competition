# Lean 4 verification — disproof of TLMC conjecture 00000000589

Pure Lean 4 core (no Mathlib). Every theorem is proved with **zero axioms and
zero `sorry`**; `Check.lean` audits this with `#print axioms`.

Contents of `Main.lean`:

- `Rep a b c m` — `m` is a nonnegative combination of `a, b, c`;
  `IsFrobenius a b c g` — `g` is the Frobenius number of `<a,b,c>`.
- `frob_family (n : Nat) (hn : 3 <= n) : IsFrobenius n (n+1) (n*n-n-1) (n*n-2*n-1)`
  — the exact Frobenius number of the attack family `<n, n+1, n^2-n-1>` is
  `n^2 - 2n - 1` for **every** `n >= 3`. This is the mathematical core: it makes
  the ratio `g / (sqrt(3) * (abc)^(1/3))` grow like `n^(2/3) / sqrt(3) -> infinity`,
  so the conjectured `sqrt(3)` bound fails by an unbounded factor.
- `frob6 / frob20 / frob100` — concrete instances `g(<6,7,29>) = 23`,
  `g(<20,21,379>) = 359`, `g(<100,101,9899>) = 9799`.
- `cert6 / cert20 / cert100` — root-free violation certificates: since
  `3*sqrt(3) < 5`, `5*abc < g^3` certifies `g > sqrt(3)*(abc)^(1/3)` (positive
  sides). E.g. `5*1218 = 6090 < 12167 = 23^3`.
- `violation6 / violation20 / violation100` — packaged counterexamples.

## Build and audit

```sh
cd lean4
lake build
lake env lean Check.lean
```

Expected: all `#print axioms` lines report "... does not depend on any axioms".

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`). No network
access or external dependencies are needed.
