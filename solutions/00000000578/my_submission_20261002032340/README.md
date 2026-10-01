# Disproof of TLMC conjecture 00000000578

**Verdict: FALSE.**

## Conjecture

`bin(n,i)` is the binary matroid on the `i`-subsets of `{1,...,n}` (represented
over GF(2) by weight-`i` 0/1 vectors); `chi_{n,i}` is its characteristic
polynomial. The conjecture claims that for all `2 <= i <= n-2` and integers
`m >= 1`, `chi_{n,i}(-m)` is divisible by `i!(n-i)!`, and that the quotient is
a nonnegative combination of Eulerian numbers.

## Attack

Characteristic polynomials are computed directly from the subset-sum
definition `chi_M(t) = sum_{X subset E} (-1)^{|X|} t^{r(E)-r(X)}` (GF(2) rank
by Gaussian elimination, cross-checked against brute-force span enumeration).

1. **bin(5,3), m = 1**: `r = 5`,
   `chi(t) = t^5 - 10t^4 + 45t^3 - 105t^2 + 120t - 51`,
   `chi(-1) = -332`, remainder `-332 mod 12 = 4`; `3!*2! = 12` does **not**
   divide `chi(-1)`.
2. **bin(6,2), m = 2**: `r = 5`,
   `chi(t) = t^5 - 15t^4 + 85t^3 - 225t^2 + 274t - 120`,
   `chi(-2) = -2520`, remainder `-2520 mod 48 = 24`; `2!*4! = 48` does **not**
   divide `chi(-2)`.

Both instances are inside the conjecture's range, so the universal claim is
false and the Eulerian-quotient part is never reached.

## Boundary

| case          | m=1            | m=2             | m=3           |
|---------------|----------------|-----------------|---------------|
| bin(4,2), mod 4  | OK          | OK              | OK            |
| bin(5,2), mod 12 | OK          | OK              | OK            |
| bin(5,3), mod 12 | FAIL (-332) | FAIL (-1263)    | OK (-3624)    |
| bin(6,2), mod 48 | OK (-720)   | FAIL (-2520)    | OK (-6720)    |

Smallest counterexample: bin(5,3) at m = 1. bin(6,2) passes at m = 1 and fails
at m = 2, so the divisibility claim is not even monotone-safe in `m`.

## Contents

- `reproduce.py` — standalone independent recomputation with assertions
  (`python3 reproduce.py`).
- `main.tex`, `build/main.pdf` — write-up (compiled with tectonic).
- `lean4/` — core-Lean formalization: GF(2) rank + full subset enumeration
  inside Lean (32,768 subsets for bin(6,2) evaluated by the kernel in
  1024-subset chunks). The attack numbers are *computed by the kernel from the
  matroid data*, not assumed. `lake env lean Check.lean` reports that every
  theorem `does not depend on any axioms` (zero axioms, zero `sorry`).

## Verdict

Conjecture 00000000578 is **false**: `12 ∤ χ_{bin(5,3)}(-1) = -332` and
`48 ∤ χ_{bin(6,2)}(-2) = -2520`.
