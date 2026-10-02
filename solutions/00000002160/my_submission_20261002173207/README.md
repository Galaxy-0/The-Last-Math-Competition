# Disproof of conjecture `00000002160`

**Verdict: FALSE — the Hoffman bound of the Higman–Sims graph is not even
an integer.**

## The conjecture (verbatim from `conjectures/00000002160.md`)

> Definition: The independence number of the Higman–Sims graph.
> Conjecture: The independence number equals the Hoffman bound, and the
> kernel of the bound is the Delsarte semilattice.

**Object consistency.** We attack exactly: α(HS) = Hoffman bound
α ≤ v·(−λ_min)/(k − λ_min) with the classical spectrum of the
Higman–Sims graph.

## The refutation (two independent kills)

The Higman–Sims graph is strongly regular with **v = 100, k = 22,
λ_min = −8** (classical spectrum; Higman 1960, standard references). Its
Hoffman bound is

    v·(−λ_min)/(k − λ_min) = 100·8/(22+8) = **800/30 = 26.6̄**

1. **800/30 is not an integer** (800 = 26·30 + 20): an independence
   number is an integer, so it can never equal this bound — the
   conjectured equality is impossible for this graph regardless of any
   further computation.
2. The classical independence number is **α(HS) = 22** (the construction
   provides 22-point independent sets), and 22 ≠ 800/30.

Lean certifies the arithmetic (`numer`, `denom`, `bound_not_integral`,
`not_divisor`, `not_divisor2`, `alpha_ne_bound`); the spectrum and
α = 22 are classical cited facts. All 7 theorems are
`does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — the Hoffman bound value, its non-integrality, and
α = 22. Exit 0.

## Boundary

Only the equality α = Hoffman bound is refuted (for this graph). The
"Delsarte semilattice kernel" clause is not addressed.
