# Disproof of conjecture `00000001186`

**Verdict: FALSE — the conjecture contradicts itself twice over, using only
its own numbers.**

## The conjecture (verbatim from `conjectures/00000001186.md`)

> Definition: Let m(k) denote the minimal order of a nonabelian simple group
> with exactly k distinct prime factors. Conjecture: m(3) = 60 (A₅), m(4) = 504
> (PSL₂(8)), m(5) = 660 (PSL₂(11)); and m(k)/m(k−1) ≤ 4 for all k, with
> equality at k = 4.

**Object-consistency note.** We attack exactly the quantities the conjecture
itself asserts ("m(3) = 60", "m(4) = 504", "m(k)/m(k−1) ≤ 4 … equality at
k = 4") — no other reading is involved.

## Refutation 1 — the ratio clause fails on the conjecture's own values

The conjecture asserts m(3) = 60 and m(4) = 504. Its ratio clause demands
m(4)/m(3) ≤ 4, i.e. 504 ≤ 4·60 = 240. But 504 > 240; the actual ratio is
504/60 = 42/5 = 8.4. So the ratio clause is violated *by the conjecture's own
stated values*, and the claimed equality case "m(4)/m(3) = 4" is impossible
(504 ≠ 240). Even the weaker bound m(4) ≤ 3·m(3) = 180 fails.

Lean: `ratio_violation`, `stronger_violation`, `ratio_numerator`.

## Refutation 2 — the stated witness m(4) = 504 does not meet the definition

m(4) is defined as the minimal order of a simple group with exactly **four**
distinct prime factors. But the conjecture's own witness satisfies

    504 = 2³ · 3² · 7

— exactly **three** distinct prime factors (2, 3, 7; certified as a
factorization by `fact504` and every prime divisor of 504 is one of these
three — see `reproduce.py` for the exhaustive divisor scan). A group of order
504 therefore cannot be a witness for m(4); the "m(4) = 504" clause is in
conflict with the definition of m(4) itself.

(The arithmetic side is documented here and in `reproduce.py`; the Lean
package certifies the factorization identity `fact504` and the ratio
violations. The prime-counting argument is one line of arithmetic on top.)

## What this does and does not claim

We only refute the literal numeric assertions as stated. The actual values of
m(k) for k ≥ 4 (e.g. m(4) = 2040, via PSL₂(16) — wait, |PSL₂(16)| = 4080 =
2⁴·3·5·17, four primes; a careful determination of m(4) is a separate
question and not needed: the conjecture is refuted by its own numbers).

## Reproduce

`python3 reproduce.py` — verifies the factorization 504 = 2³·3²·7, the
distinct-prime count (3), the divisor scan (every prime divisor of 504 is in
{2,3,7}), and 504 > 240. Exit 0 iff all checks pass.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — all 5 theorems
`does not depend on any axioms`.
