# Lean verification for the disproof of TLMC conjecture 00000000325

Core Lean 4 only (no Mathlib).  `Main.lean` formalizes the arithmetic core
of the attack: at τ = 1/2 the conjectured packing dimension 2/(1+1/2) = 4/3
exceeds the ambient dimension 1 of ℝ (`Tlmc325.attack`), and more generally
the conjectured value 2q/(p+q) exceeds 1 whenever τ = p/q < 1
(`Tlmc325.claimed_exceeds_ambient`).  Two mismatch theorems record that the
claimed value disagrees with the true (Khinchin–Jarník) values at τ = 2 and
τ = 1/4.  All proofs are pure kernel computations on ℕ — zero axioms, zero
`sorry`.

## Build and audit

```sh
export ELAN_HOME=<your elan dir>
export PATH="$ELAN_HOME/bin:$PATH"
lake build
lake env lean Check.lean
```

Every `#print axioms` line must report `does not depend on any axioms`.
