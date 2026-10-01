# Disproof of TLMC conjecture 00000000119

**Verdict: FALSE.**

## Conjecture

There are infinitely many primes `p` for which the Pisano period `pi(p)`
(the period of the Fibonacci sequence modulo `p`) is itself prime.

## Disproof

The set of primes `p` whose Pisano period `pi(p)` is prime is exactly
`{2}` — a single prime, so certainly not infinitely many.

The referee's data already shows `pi(2) = 3` (prime) and `pi(3) = 8`,
`pi(5) = 20`, `pi(7) = 16` (all even). The obstruction generalizes:

* Let `Q = [[1,1],[1,0]]`, so `det Q = -1` and `Q^m = [[F(m+1), F(m)], [F(m), F(m-1)]]`.
* If `n` is a period of the Fibonacci sequence mod `p` (`F(n) = 0`,
  `F(n+1) = 1` mod `p`), then `Q^n = I` mod `p`, so `det(Q^n) = (-1)^n = 1`
  mod `p`. For `p >= 3` this forces `n` to be **even**.
* `pi(p) = 2` is impossible: `F(2) = 1` is not `0` mod `p >= 2`.
* Hence for every `p >= 3` (primality of `p` is not even needed) the period
  `pi(p)` is even and `> 2`, therefore **not prime**.
* `p = 2` survives: `pi(2) = 3`, which is prime.

## The Lean development (`lean4/`)

Core Lean 4 only (no Mathlib), **zero axioms** — every declaration is
`#print axioms`-audited in `Check.lean` and none depends on anything.
To keep the audit clean the development avoids `omega`, `simp` and
`decide` on symbolic goals (those tactics pull in `propext`/`Quot.sound`);
all arithmetic is structural induction plus explicit rewriting, and all
congruences are phrased existentially (`fib n = p * a`,
`fib (n+1) = p * b + 1`), avoiding `%`/`/` theory entirely.

Key declarations:

* `period_even` : for every `p >= 3` and every period `n` of the Fibonacci
  sequence mod `p`, `n` is even and `n != 2` (universality of the attack;
  primality of `p` is not needed).
* `only_two` : if `p` and `n` are primes and `n` is a period mod `p`, then
  `p = 2`.
* `cassini_even`, `cassini_odd` : Cassini's identity `F(n+1)^2 - F(n)F(n+2) = (-1)^n`,
  the engine of the parity obstruction (proved by a two-step induction).
* `pisano2, ..., pisano13` : the referee's numbers `pi(2)=3, pi(3)=8,
  pi(5)=20, pi(7)=16, pi(11)=10, pi(13)=28`, each a single `rfl`
  computation that also verifies minimality and the wrap-around.

## Reproduce

```
cd lean4 && lake build && lake env lean Check.lean
python3 reproduce.py
```

`reproduce.py` recomputes `pi(p)` for the referee's data points, verifies
that the only prime below 2000 whose Pisano period is prime is `2`, and
checks that all other primes below 2000 have even `pi(p)`.

## Scope

The disproof is unconditional and self-contained; no version of the
conjecture survives (the set in question is provably `{2}`).
