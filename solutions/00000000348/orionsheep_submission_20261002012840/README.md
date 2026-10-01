# Disproof of Conjecture 00000000348

**Verdict: FALSE.**

## Conjecture (restated)

There exists a real number alpha whose continued-fraction partial quotients satisfy

  a_n = a_{n+1} = floor(tau(n))   for all n >= 1,

where tau(n) is the divisor function (number of positive divisors of n); moreover alpha
is given by an explicit series construction.

## Attack

The constraints for consecutive n overlap in one variable. For n and n+1 both require
the same partial quotient a_{n+1}:

  from n:     a_{n+1} = floor(tau(n))
  from n+1:   a_{n+1} = floor(tau(n+1))

So a single alpha can exist only if floor(tau(n)) = floor(tau(n+1)) for every n >= 1.

Registered attack point: n = 4, 5.

  tau(4) = |{1, 2, 4}| = 3,  so n = 4 forces  a_4 = a_5 = 3.
  tau(5) = |{1, 5}|    = 2,  so n = 5 forces  a_5 = a_6 = 2.

Hence a_5 = 3 and a_5 = 2 simultaneously -- contradiction. No real number alpha (let
alone one built by an explicit series) can satisfy the stated partial-quotient pattern.

Recomputed independently (see reproduce.py): tau(4) = 3, tau(5) = 2, conflict at a_5
confirmed. This matches the pipeline attack point and the CONFIRMED verdict.

## Boundary notes

- The contradiction arises even earlier: n = 1, 2 give a_2 = tau(1) = 1 and
  a_2 = tau(2) = 2. The registered attack (n = 4, 5) is used as primary; the Lean
  formalization kills the existential using the n = 4 / n = 5 constraints.
- In general the conjecture's condition forces tau(n) = tau(n+1) for all n >= 1, i.e. a
  constant divisor function, which is false (tau(1) = 1 != 2 = tau(2)); any adjacent
  pair with differing tau yields a disproof.
- The floor is immaterial here: tau(n) is an integer, so floor(tau(n)) = tau(n).
- Scope: this disproves existence for the stated "for all n" reading of the conjecture,
  which is how the conjecture text ("a_n = a_{n+1} = floor(tau(n))" holding for the
  sequence) is to be understood. If the intended statement were the much weaker
  "there exists some n with a_n = a_{n+1} = floor(tau(n))", the statement would be
  trivially true for many alpha and not the conjecture as written.

## Contents

- `main.tex` / `build/main.pdf`: 1-page disproof note.
- `reproduce.py`: standalone recomputation of the attack numbers.
- `lean4/`: zero-axiom Lean 4 (no Mathlib) formalization. `Main.lean` proves
  `¬ ∃ a : ℕ → ℕ, ∀ n, a n = tau n ∧ a (n+1) = tau n`. Run `lake build && lake env lean Check.lean`;
  Check.lean prints the axiom profile of every theorem (must be "does not depend on any axioms").
