# TLMC conjecture 00000000122 — Disproof

**Verdict: FALSE.**

## Conjecture

For every `n ≥ 2` there exist infinitely many primes `q` such that the `n`-th
`q`-Catalan number `C_n(q)` is prime.

## Attack (n = 2)

**Standard (Gaussian-binomial) reading** `C_n(q) = [2n choose n]_q / [n+1]_q`:
`C_2(q) = [4 choose 2]_q / [3]_q = (1+q^2)(1+q+q^2) / (1+q+q^2) = q^2 + 1`.
For every odd prime `q`, `q^2 + 1` is even and `≥ 10`, hence composite. The
only prime that can survive is `q = 2`, and `C_2(2) = 5` is indeed prime. So
for `n = 2` there is **exactly one** prime `q`, not infinitely many.

**Carlitz reading** (`C_0 = 1`, `C_{n+1} = Σ_k q^k C_k C_{n-k}`):
`C_2(q) = 1 + q`. For every odd prime `q`, `q + 1` is even and `≥ 4`, hence
composite. Again the only survivor is `q = 2` with `C_2(2) = 3` prime.

Both common readings of "`C_n(q)`" collapse the `n = 2` instance to a single
witness, so the universally quantified conjecture is **false**.

## Boundary

* The counterexample is `n = 2` only; no claim is made about `n ≥ 3` (those
  instances remain open under both readings).
* The classification is exact: for prime `q`, `C_2(q)` is prime **iff**
  `q = 2` (`C_2(2) = 5` resp. `C_2(2) = 3`, both proved prime). Formalized as
  `C2_prime_iff_eq_two` / `C2Carlitz_prime_iff_eq_two` in the Lean certificate.

## Contents

* `main.tex`, `build/main.pdf` — formal write-up.
* `reproduce.py` — standalone Python recomputation (exact polynomial
  Gaussian-binomial division and the Carlitz recurrence; primality by trial
  division). Run `python3 reproduce.py`.
* `lean4/Main.lean` — Lean 4 certificate (core Lean, no Mathlib, toolchain
  `leanprover/lean4:v4.33.1`): headline theorems
  `tlmc122_disproof_standard` and `tlmc122_disproof_carlitz`.
* `lean4/Check.lean` — axiom audit: every theorem prints
  `does not depend on any axioms` (zero axioms, zero `sorry`).

## Lean build

```sh
cd lean4
lake build
lake env lean Check.lean
```
