# Disproof of conjecture `00000002149`

**Verdict: FALSE at the conjecture's own tight case.**

## The conjecture (verbatim from `conjectures/00000002149.md`)

> Definition: The Colin de Verdière parameter μ(G) is the spectral-rigidity
> invariant of a graph. Conjecture: μ(Ḡ) ≤ |V| − ω(G) − 1 (an upper bound for
> the complement); the bound is tight (attained by the complete graph with
> empty complement).

**Object consistency.** We attack exactly the inequality μ(Ḡ) ≤ |V| − ω(G) − 1
at the case the conjecture itself names as the tight one: G = K_n.

## The refutation

Take **G = K_n** (n ≥ 2), the conjecture's own "tight" case:

- Ḡ = the **edgeless graph** on n vertices;
- ω(K_n) = n, so the bound's right side is **n − n − 1 = −1**;
- the classical value of the Colin de Verdière parameter of the edgeless
  graph (n ≥ 2) is **μ = 0** (no edges ⟹ no admissible nonzero matrix;
  Colin de Verdière 1990 and standard references).

The claimed inequality is therefore **0 ≤ −1: FALSE** at the very case the
conjecture asserts attains equality. (For the record, the true tight cases
of μ(Ḡ) ≤ |V| − ω(G) − 1-type statements involve nonnegativity of μ; a bound
that is negative cannot ever hold since μ ≥ 0 always.)

Lean certifies the arithmetic (−1 < 0, μ = 0 ≥ 0, ¬(0 ≤ −1)); the classical
value μ(edgeless) = 0 is cited in README/tex with its justification.

## Reproduce

`python3 reproduce.py` — the arithmetic n − n − 1 = −1 < 0 ≤ μ(empty) = 0 for
n = 2..10, plus the statement of the classical value. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 3 theorems, all
`does not depend on any axioms`.
