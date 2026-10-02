# Disproof of conjecture `00000002181`

**Verdict: FALSE at n = 1 (base-independent).**

## The conjecture (verbatim from `conjectures/00000002181.md`)

> Definition: The Gotsman–Linial conjecture relates the sensitivity of
> Boolean functions to their spectral norm. Conjecture: Sensitivity is
> always at most √2·log n times the spectral norm; and the bound is
> controlled by the pointer maxima of real hypercubical faces.
> (sensitivity spectral-norm sqrt-two law)

**Object consistency.** We attack exactly: sensitivity ≤ √2 · log(n) ·
‖f̂‖₁ (Fourier ℓ¹ spectral norm) for Boolean functions on the n-cube, at
n = 1.

## The counterexample (the 1-cube)

Take **f = NOT**: f(0) = 1, f(1) = −1. Its Fourier coefficients
(f̂(S) = ½ Σₓ f(x)·χ_S(x)):

    f̂(∅)  = (1 + (−1))/2        = 0
    f̂({1}) = (1·1 + (−1)·(−1))/2 = 1

so ‖f̂‖₁ = 0 + 1 = **1**. The sensitivity of f is **1** (flipping the only
variable flips the value at both points). The conjectured bound at n = 1:

    √2 · log(1) · 1 = √2 · 0 = **0**   (log 1 = 0 in every base)

and the claimed inequality is **1 ≤ 0 — false**, independently of the
logarithm base and of the constant √2.

(The plain enumeration at n = 2 under the natural logarithm also yields
violations — see `reproduce.py` — but the n = 1 case alone suffices and is
base-free.)

## Reproduce

`python3 reproduce.py` — computes the two Fourier coefficients and the
sensitivity on the 1-cube, the bound value 0, and also enumerates all 16
Boolean functions on the 2-cube under the natural logarithm and reports
the violators. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 6 theorems,
all `does not depend on any axioms` (arithmetic of the coefficients 0/2
and 2/2, the norm 1, sensitivity 1, bound 0, ¬(1 ≤ 0)).

## Boundary

Only the n = 1 case is formalized (it is base-free); the n = 2 checks are
in `reproduce.py` only. The "pointer maxima" clause is not addressed.
