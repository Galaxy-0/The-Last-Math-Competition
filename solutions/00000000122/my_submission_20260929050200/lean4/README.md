# Lean certificate for the disproof of TLMC conjecture 00000000122

Core Lean 4 (no Mathlib), toolchain `leanprover/lean4:v4.33.1`.

## Contents

- `Main.lean` — the formalization. `IsPrime` is a self-contained primality
  predicate; `C2 q = q*q + 1` is the standard (Gaussian-binomial) q-Catalan
  `C₂`, `C2Carlitz q = q + 1` the Carlitz one. Key theorems:
  - `not_prime_C2_of_odd : q % 2 = 1 → 3 ≤ q → ¬ IsPrime (C2 q)`
  - `not_prime_C2Carlitz_of_odd : q % 2 = 1 → 3 ≤ q → ¬ IsPrime (C2Carlitz q)`
  - `C2_prime_iff_eq_two`, `C2Carlitz_prime_iff_eq_two`: for prime `q`,
    `C₂(q)` is prime **iff** `q = 2` (the unique witness is genuine:
    `C₂(2) = 5` resp. `3`, both proved prime).
  - `tlmc122_disproof_standard`, `tlmc122_disproof_carlitz`: headline
    statements — at most one prime `q` works for `n = 2`, so "infinitely many"
    fails and conjecture 00000000122 is FALSE.

## Build and axiom audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem; every line must read
`... does not depend on any axioms` (zero axioms, zero `sorry`).
