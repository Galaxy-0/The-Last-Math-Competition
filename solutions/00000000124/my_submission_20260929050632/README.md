# Disproof of TLMC Conjecture 00000000124

**Verdict: FALSE.**

## The conjecture

Let `q` be an odd prime such that 2 is a primitive root mod q; then the least
positive integer `m(q)` missing from the orbit `{2^n mod q : n >= 0}` satisfies
`m(q) = O((log q)^2)`.

## The attack

Structural, no computation needed. If `ord_q(2) = q-1`, the `q-1` residues
`2^0, ..., 2^(q-2)` are pairwise distinct nonzero residues, hence exactly
`{1, ..., q-1}`; the value `q` (residue 0) never occurs. Therefore

> **m(q) = q identically**, and `q > (log q)^2` for every `q >= 3`.

Spot checks from the verification verdict, reproduced exactly:

- `q = 3`: orbit `{1,2}`, `m(3) = 3 > (ln 3)^2 = 1.2069...`
- `q = 101`: orbit `= {1..100}`, `m(101) = 101 >> (ln 101)^2 = 21.2993...`

In fact `m(q) = q > (ln q)^2` holds at **every** admissible prime (the
conjecture fails with constant `C = 1` unconditionally, everywhere), and for
every fixed `C > 0` at every admissible `q > e^(6C)` (since `e^L >= L^3/6`
gives `q > C(ln q)^2` whenever `ln q > 6C`). The true growth of `m(q)` is
linear in `q`, not polylogarithmic.

## Boundary (scope of the refutation)

- **Unconditional**: `m(q) = q` exactly; `m(q) > (log q)^2` with `C = 1` for
  every admissible `q`; violation for any fixed `C` once `q > e^(6C)`.
- **Conditional extra step**: refuting the big-O for *arbitrary* `C` needs
  unboundedness of the admissible primes, i.e. Artin's primitive-root
  conjecture for `a = 2` (open; provable under GRH [Hooley 1967]; expected
  density ~0.374, OEIS A001122). If the admissible set were finite, the
  O-statement would hold vacuously for large `q` — this is the only gap, and
  it does not affect the exact identity `m(q) = q` or the unconditional `C = 1`
  refutation.

## Files

- `main.tex`, `build/main.pdf` — formal write-up (theorem, proof, boundary,
  computational table for all 22 admissible primes below 200).
- `reproduce.py` — independent recomputation, pure standard library:
  `python3 reproduce.py` (optional numeric bound argument, default 200).
  Recomputes primality, orders, orbits, least-missing values, the verdict's
  spot checks, and prints the discrete-log witness lists used by Lean.
- `lean4/` — self-contained Lean 4 project (core Lean only, toolchain
  `leanprover/lean4:v4.33.1`); see `lean4/README.md`.

## Lean axiom audit

`lake build` then `lake env lean Check.lean` prints, for **all 138 theorems**:

```
'...' does not depend on any axioms
```

138/138 clean — zero `sorry`, zero `propext`, zero `Quot.sound`, zero
`Classical.choice`. All computational claims are `decide`-checked over `Nat`;
the two bridging lemmas (`dlogOk_implies`, `not_inOrbit_self`) are proved by
hand from core `Nat`/`List` lemmas.
