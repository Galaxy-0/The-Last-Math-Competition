# Lean 4 verification (no Mathlib, zero axioms)

`Main.lean` formalizes the disproof of conjecture 00000000348:

- `tau` is the divisor function (count of positive divisors), plain core Lean.
- `tau_four : tau 4 = 3` and `tau_five : tau 5 = 2` hold by `rfl`.
- `no_such_alpha : ¬ ∃ a : ℕ → ℕ, ∀ n, a n = tau n ∧ a (n+1) = tau n` — the
  conjecture's partial-quotient condition is unsatisfiable, because `n = 4` forces
  `a 5 = 3` while `n = 5` forces `a 5 = 2`.

## Build and audit

```
lake build
lake env lean Check.lean
```

`Check.lean` prints the axiom profile of each theorem; all three report
"does not depend on any axioms" (no `sorry`, no `Classical.choice`, no `propext`,
no `Quot.sound`, no `Lean.ofReduceBool`).
