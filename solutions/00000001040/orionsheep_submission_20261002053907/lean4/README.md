# Lean 4 verification for the disproof of conjecture 00000001040

Pure core Lean 4 (no Mathlib). All claims are finite computations over
F_5 discharged by `decide` (kernel reduction).

## Contents

- `Main.lean` — definitions (`isPerm5`, `linCM`, `cmsCount`, `cubeFamFails`)
  and theorems, culminating in `TLMC1040.disproof_00000001040`:
  * q = 5 satisfies 5 = 2 (mod 3);
  * f(x) = 2x is a complete mapping (2x and 3x both permutations of F_5);
  * x^3 + x is not a permutation (x = 0, 2, 3 collide at 0);
  * no A*(x+B)^3 (A in F_5^x, B in F_5) is a complete mapping;
  * exactly 15 linear complete mappings exist (slopes a in {1,2,3}),
    enumerated explicitly.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints the axiom profile of every theorem; each line must read
"does not depend on any axioms". There are no `sorry`s and no
`native_decide`.
