# Lean 4 verification — Disproof of conjecture 00000000544

Core Lean 4 only (no Mathlib). **Zero axioms, zero `sorry`.**

- `Main.lean` — formalization of the single-edge forest `K_2` attack:
  the lattice `ker_Z([[1],[1]])` is trivial (`{0}`), so the Graver basis is
  empty (`|Graver| = 0`), while the forest bound on `K_2` is `8 >= 4`;
  `conjecture_544_fails` certifies that the equality-on-forests clause fails.
- `Check.lean` — `#print axioms` audit of every theorem plus independent
  sanity re-checks.

## Build and verify

```sh
lake build
lake env lean Check.lean
```

Expected: every line reports `... does not depend on any axioms`.

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
