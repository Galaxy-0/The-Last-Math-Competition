# Lean 4 verification — disproof of conjecture 00000000423

Core Lean 4 only (no Mathlib). `Main.lean` formalizes the attack on shape
`(2,1)`:

* `syt21s_eq` — the SYT of shape `(2,1)` are exactly `(1,2,3)` and `(1,3,2)`;
* `prom_A`, `prom_B` — Schutzenberger promotion swaps them;
* `prom_involutive`, `A_ne_B` — the single orbit has length exactly `2`;
* `three_mod_two`, `two_not_dvd_three` — `2 ∤ 3` (tableau size `n = 3`);
* `conjecture_00000000423_false` — the conjunction of the attack assertions.

## Build and audit

```
lake build
lake env lean Check.lean
```

Every `#print axioms` line in the `Check.lean` output must read
`does not depend on any axioms`. There are no `sorry` anywhere.

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
