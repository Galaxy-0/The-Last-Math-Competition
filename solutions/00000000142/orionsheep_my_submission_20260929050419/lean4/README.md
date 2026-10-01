# Lean 4 concretization (bare Lean 4.33.1, no Mathlib)

Machine-checks the exact finite-n assertions used in the disproof of TLMC
conjecture 00000000142.

## Build and audit

```bash
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem; all 18 lines must read
`does not depend on any axioms`. No `sorry` anywhere.

## Contents (Main.lean)

| theorem | statement | meaning for the attack |
|---|---|---|
| `diag_eq_one` | `diag n = 1` for `n >= 1` (general proof) | `tr M_n = 1`: only `i=1` has `2i` prime; ESD mean `= 1/n` |
| `diag_1000` | `diag 1000 = 1` (`decide`) | instance |
| `traceSq_eq_pairCount` | `traceSq n = pairCount n` (general proof) | `tr M_n^2 = N(n)` since entries are 0/1 and `M` is symmetric |
| `pairCount_8/64/128` | `N(n) = 23 / 941 / 3239` (`decide`) | exact prime-pair counts |
| `moment_gt_one_64/128` | `n < pairCount n` (`decide`) | ESD second moment `N(n)/n > 1` already at n=64 (semicircle value is 1) |
| `moment_growth` | `64 * N(128) > 128 * N(64)` (`decide`) | second moment grows: `N(128)/128 = 25.3 > N(64)/64 = 14.7` |

Supporting lemmas: `bev`/`bev_add_self`/`bev_two_mul` (axiom-free evenness),
`even_composite` (`isPrime (2*i) = false` for `i >= 2`), `entry_sym`,
`entry_mul_sym` (`M_ij M_ji = M_ij`), `trRow_eq_rowSum`, `trSq_eq_pc_aux`.

## Proof discipline (why zero axioms)

`omega`, `simp`, `native_decide` are avoided (they emit `propext`/`Quot.sound`/
`Lean.ofReduceBool`). All proofs use `rfl`, `decide` (kernel computation, axiom-free),
explicit `Eq.trans`/`congrArg`/`Eq.subst` term proofs, and structural induction.
Evenness is decided by the custom two-step-recursive `bev` so that no `Nat.mod`
lemma (the core ones carry `propext`) is needed on the proof path.
