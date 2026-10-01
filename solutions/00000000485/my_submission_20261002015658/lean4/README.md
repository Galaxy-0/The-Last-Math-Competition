# Lean 4 check for the disproof of conjecture 00000000485

Core Lean only (no Mathlib).  `Main.lean` contains a computable model of the
Murnaghan–Nakayama value of the irreducible characters of `S_n` at the long
cycle `c_n`:

- `parts n` — the exact enumeration of partitions of `n`
  (verified: `(parts 10).length = 42`, `(parts 12).length = 77`, and every
  enumerated partition sums to `n`);
- `chiCycle lam` — the character value at an n-cycle: `(-1)^(height-1)` when
  `lam` is a border strip (hook), `0` otherwise (the Murnaghan–Nakayama rule
  for a rim hook of size `n` = the whole diagram);
- `badCount n` — the number of shapes `lam |- n` with `|chi| > 1`.

The theorems prove by pure kernel reduction (`rfl`) that `badCount n = 0`
for `n = 3..12`, i.e. the proportion of shapes with `|chi_lambda(c_n)| > 1`
is identically `0` — the conjecture is false.

## Build and verify

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints the axiom profile of every theorem; each reports
*"does not depend on any axioms"* (zero axioms, zero `sorry`).
