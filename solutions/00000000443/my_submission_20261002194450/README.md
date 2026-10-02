# Disproof of conjecture `00000000443`

**Verdict: FALSE at n = 5 (a prime).**

## The conjecture (verbatim from `conjectures/00000000443.md`)

> Definition: The n-th homogeneous dimension of the free Lie algebra L(V)
> is given by Witt's formula (1/n)Σ_{d|n}μ(d)k^{n/d}. Conjecture: For k = 2
> and all n ≥ 2, dim L_n ≥ 2^{n−1} − 2^{⌈n/2⌉}, and for n prime the gap
> between this bound and the exact value is exactly half of 2^{(n−1)/2}.

**Object consistency.** We attack exactly the displayed lower bound with
dim L_n given by the conjecture's own Witt formula.

## The refutation

At **n = 5** (prime), Witt's formula (the conjecture's own definition;
divisors of 5 are 1 and 5, μ(1)=1, μ(5)=−1) gives

    dim L₅ = (2⁵ − 2)/5 = 30/5 = **6**,

while the conjectured lower bound is

    2⁴ − 2^{⌈5/2⌉} = 16 − 8 = **8**.

The claimed inequality is **6 ≥ 8: FALSE**. Since n = 5 is prime, the
prime-gap clause collapses with the bound.

## Reproduce

`python3 reproduce.py` — Witt's formula for n = 2..12 (exact), the bound,
and the violations (n = 5, and also n = 7: 18 ≥ 56 fails etc.). Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 4 theorems
(`numer`, `witt_5`, `bound_5`, `violated`), all
`does not depend on any axioms`.

## Boundary

The lower-bound clause is refuted at n = 5 (and further primes per
reproduce); the gap clause is moot once the bound fails.
