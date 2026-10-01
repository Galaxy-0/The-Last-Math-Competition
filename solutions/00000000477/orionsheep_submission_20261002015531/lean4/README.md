# Lean 4 verification for the disproof of conjecture 00000000477

Pure core Lean 4 (no Mathlib). Toolchain: `leanprover/lean4:v4.33.1`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

Expected: `lake build` succeeds with no errors/sorries, and every
`#print axioms` line in the `Check.lean` output reports
`does not depend on any axioms` (zero `propext`, zero `Quot.sound`,
zero `Classical.choice`).

## What is proved

`Main.lean` concretises the attack against conjecture 00000000477
("the lcm of promotion orbit lengths on LE(P) divides #LE(P)"):

- brute-force enumeration (`syts_eq`) shows the Ferrers poset of shape (3,2)
  has exactly 5 linear extensions (`card_LE`), namely the 5 standard tableaux
  `t1..t5`;
- Schutzenberger promotion is implemented explicitly (`pr`, jeu de taquin for
  this fixed shape) and `pr_t1..pr_t5` pin down its action:
  `t1 -> t3 -> t4 -> t1` (orbit of length 3, `orbit_A`) and
  `t2 -> t5 -> t2` (orbit of length 2, `orbit_B`);
- `lcm_eq`: `Nat.lcm 3 2 = 6`; `not_divides`: `6` does not divide `5`;
- `counterexample_00000000477` bundles these into the falsifying witness.

All proofs are `decide`/`rfl` on explicit data; the brute-force enumeration
over the 3125 candidate tuples runs in the kernel under
`set_option maxHeartbeats 1000000`.
