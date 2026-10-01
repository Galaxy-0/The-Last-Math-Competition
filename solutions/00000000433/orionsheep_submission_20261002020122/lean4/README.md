# Lean verification for the disproof of conjecture 00000000433

Core Lean 4 only (no Mathlib). `Main.lean` formalizes the B2 attack:

- `WeylB2` — the 8 elements of the Weyl group of B2 as signed coordinate
  permutations on `Int × Int`;
- `rhoB2 = (3, 1)` — the Weyl vector `rho(B2) = (3/2, 1/2)` rescaled by 2
  (scaling is a bijection, so distinctness of `w(rho) - rho` is preserved);
- `exponentsB2` — the 8 exponents `w(rho) - rho`, computed to be
  `[(0,0), (-6,0), (0,-2), (-6,-2), (-2,2), (-4,2), (-2,-4), (-4,-4)]`
  (twice the values in the write-up);
- `exponentsB2_pairwise_distinct` — no two exponents coincide, so the
  denominator identity has no cancellable/mergeable terms: T(B2) = 8;
- `T_B2` — the count is exactly 8;
- `conjecture_00000000433_B2_false` — `T(B2) = 2` is impossible.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem. Expected result: each
one reports **"does not depend on any axioms"** (no `propext`, no
`Quot.sound`, no `Classical.choice`; no `sorry`; no `native_decide`).
