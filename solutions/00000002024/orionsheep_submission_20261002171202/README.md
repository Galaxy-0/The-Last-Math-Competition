# Disproof of conjecture `00000002024`

**Verdict: FALSE — the conjecture's own k = 4 exception clause asserts 19 > 19.**

## The conjecture (verbatim from `conjectures/00000002024.md`)

> Definition: g(k) is the Waring number for all positive integers (every n is
> a sum of s k-th powers). Conjecture: The exceptions to
> g(k) = 2^k + ⌊(3/2)^k⌋ − 2 are finite, with the largest exception k = 4
> (**g(4) = 19 > 2⁴ + ⌊(3/2)⁴⌋ − 2**); for k ≥ 5 the formula always holds.

**Object consistency.** We attack exactly the parenthetical numeric claim:
g(4) versus the formula's value at k = 4, with g(4) = 19 taken from the
conjecture's own text (it is also the classical theorem of
Balasubramanian–Deshouillers–Dress, 1986).

## The refutation (one line of arithmetic)

    2⁴ + ⌊(3/2)⁴⌋ − 2 = 16 + ⌊81/16⌋ − 2 = 16 + 5 − 2 = 19 = g(4).

The strict inequality g(4) > 2⁴ + ⌊(3/2)⁴⌋ − 2 is therefore 19 > 19 —
false. k = 4 is **not** an exception: the formula holds at k = 4 with
equality, so "the largest exception k = 4" is wrong, and with it the
conjecture's stated exception structure.

Lean: `floor_3halves_4` (⌊81/16⌋ = 5), `formula_at_4` (16 + 5 − 2 = 19),
`strict_inequality_false` (¬(19 > 19)) — all `does not depend on any axioms`.

## Boundary

Only the k = 4 exception clause (with the conjecture's own g(4) = 19) is
refuted. The finiteness claim and the k ≥ 5 clause are separate assertions
not needed for this disproof.

## Reproduce

`python3 reproduce.py` — checks ⌊(3/2)⁴⌋ = 5, the formula value 19, and
19 > 19 false; also cross-checks that 79 requires 19 fourth powers and
that 2⁴·15 = 240 needs 19 (spot checks of g(4) = 19). Exit 0 iff pass.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 4 theorems,
all axiom-free.
