# Lean formalization — disproof of TLMC conjecture 00000000404

Core Lean only (no Mathlib, no external dependencies). All proofs are
`rfl`/`decide` on explicit integer arithmetic; the axiom audit
(`lake env lean Check.lean`) reports that every theorem depends on **no
axioms** (in particular no `sorry`, no `propext`, no `Quot.sound`, no
`Classical.choice`, no `Lean.ofReduceBool`).

## What is formalized

Degree-4 symmetric functions in the power-sum basis
`(p1111, p211, p31, p22, p4)`, stored with common denominator 8.

1. `attack_expansion` — the lambda-ring identity
   `s2[f] = (f*f + psi^2(f))/2` applied to `f = s2 = (p1^2 + p2)/2`
   gives, in the power-sum basis,

      s_{(2)}[s_{(2)}] = (p1111 + 2 p211 + 3 p22 + 2 p4) / 8.

2. `character_table_orthogonal` — the S4 character table used below is
   column-orthonormal (weighted by class sizes 1,6,8,3,6), so it is a
   genuine character table.

3. `conjecture_404_false` — Hall-orthogonality extraction
   `c_nu = sum_rho a_rho chi^nu(rho)` yields

      c_(4)     = 1   (ODD)
      c_(3,1)   = 0
      c_(2,2)   = 1   (ODD)
      c_(2,1,1) = 0
      c_(1^4)   = 0

   hence `s_{(2)}[s_{(2)}] = s_{(4)} + s_{(2,2)}` and the coefficient of
   even-indexed nu (|nu| even, all parts even, first part even, and for
   nu=(2,2) also even length) is 1, not even — the conjecture fails.

4. `parity_odd` — the two nonzero coefficients are odd (`% 2 = 1`).

5. `dim_check` — the Weyl dimension cross-check for GL4:
   `dim Sym^2(Sym^2 C^4) = C(11,2) = 55 = C(7,4) + 20 = dim s_(4) + dim s_(2,2)`.

6. `boundary_n1` — at n = 1, `s2[s1] = s_(2)` with coefficient 1 (odd):
   the failure is not an n = 2 accident.

## Build and audit

```
lake build
lake env lean Check.lean
```

Expected: every `#print axioms` line ends with
*does not depend on any axioms*.

(If elan lives in a nonstandard place:
`export ELAN_HOME=<elan dir> && export PATH="$ELAN_HOME/bin:$PATH"` first.)
