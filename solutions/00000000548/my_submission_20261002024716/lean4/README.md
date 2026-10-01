# lean4 — axiom-free formalization of the attack on 00000000548

Pure core Lean 4, no Mathlib, no `sorry`, no axioms.

`Main.lean` formalizes the counterexample `(xyz) = (x) ∩ (y) ∩ (z)` in
`k[x,y,z]`:

* `decomposition_correct` — pointwise set equality of monomial ideals;
* `component_{x,y,z}_needed` — irredundancy witnesses `yz`, `xz`, `xy`;
* `mem{X,Y,Z}_irreducible` — each component admits no decomposition into two
  strict monomial super-ideals (constructive `u + v` argument);
* `generated_by_one`, `nonempty` — `β₀((xyz)) = 1`;
* `main`, `iota_gt_beta0` — the numbers: `ι = 3 > 1 = β₀`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` runs `#print axioms` on every theorem; each must print
`does not depend on any axioms`. In particular no `propext`, `Quot.sound`,
`Classical.choice` or `sorryAx` is used: membership predicates are
`Bool`-valued, equalities are proved by `rfl`/`decide` over concrete `Bool`
algebra, and no `funext` is needed.

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
