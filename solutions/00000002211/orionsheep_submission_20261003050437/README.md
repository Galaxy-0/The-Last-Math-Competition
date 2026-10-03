# Disproof of conjecture `00000002211`

**Verdict: FALSE — ρ(Z[√−6]) = 1 and ρ(Z[√−14]) > 1, yet 6 and 14 have
the same smallest prime factor 2. The elasticity of Z[√−d] is not
determined by spf(d), so no "table indexed by the smallest prime
factor of d" can be correct.**

## The conjecture (verbatim from `conjectures/00000002211.md`)

> Definition: The elasticity ρ(R) is the ratio of longest to shortest
> factorizations. Conjecture: For imaginary quadratic integer rings
> Z[√−d], ρ has an explicit table of the type (smallest prime factor
> of d) (a quadratic-order elasticity table).

## The refutation

The two rings Z[√−6] and Z[√−14] are the full rings of integers of
Q(√−6) and Q(√−14) (d ≡ 2 mod 4), with discriminants −24 and −56.
Their class numbers, computed by exhausting the reduced positive-
definite binary quadratic forms:

* h(−24) = 2 — the reduced forms are exactly (1,0,6) and (2,0,3).
* h(−56) = 4 — the reduced forms are exactly (1,0,14), (2,0,7),
  (3,2,5) and its mirror (3,−2,5) (the form (3,2,5) has 0 < |b| < a <
  c, so it is not self-converse and contributes a distinct inverse
  class).

By Carlitz's theorem (1960), a ring of integers is half-factorial
(ρ = 1) if and only if its class number is at most 2. Hence

    ρ(Z[√−6])  = 1        (h = 2 ≤ 2)
    ρ(Z[√−14]) > 1        (h = 4 > 2)

while 2 = spf(6) = spf(14) (both d are even, and 2 is the smallest
prime). A function of spf(d) must take equal values at 6 and 14; ρ
does not. The conjectured table does not exist.

## Verification

* `reproduce.py` — independent recomputation of the reduced-form
  exhaustions (class numbers 2 and 4, form lists as above), the
  shared smallest prime factor, and the size-bound sanity check
  3a² ≤ |D| used by the Lean enumeration.
* Lean 4 (core, v4.33.1), `lean4/` — the full reduced-form
  enumerations for both discriminants are kernel-certified: every
  solution of 4ac = b² + 24 (resp. b² + 56) with 1 ≤ a, b ≤ a, a ≤ c
  is proved to be one of the listed triples, with each (a,b) leaf
  closed by an explicit divisibility two-sided bound; plus the
  strictness 0 < 2 < 3 < 5 and the comparison 2 ≤ 2 < 4. All 6
  audited theorems report `does not depend on any axioms`. (Core
  lemmas Nat.mul_assoc / Nat.add_mul / Nat.mul_mod_right depend on
  axioms, so associativity and cancellation helpers are rebuilt by
  induction inside the package.)

## Boundary

The Lean kernel certifies the class-number data (as reduced-form
enumerations), the shared spf, and the numeric comparison. Carlitz's
half-factorial criterion (h ≤ 2 ⟺ ρ = 1 for rings of integers), the
reduction-theory identification "class number = number of reduced
primitive positive-definite forms", and the reflection pairing
b ↔ −b are classical results cited in prose. The refutation of the
stated table claim is complete; no claim is made about elasticity
tables indexed by other invariants.
