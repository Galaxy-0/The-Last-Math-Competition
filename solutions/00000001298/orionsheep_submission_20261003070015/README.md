# Disproof of conjecture `00000001298`

**Verdict: FALSE — the formal solution of the q-difference equation
f(qx) − f(x) = x^k is unique, f = x^k/(q^k − 1), and its coefficient
1/(q^k − 1) is a non-integer rational for all q ≥ 2, k ≥ 2, while
q-binomial coefficients are polynomials in q (hence integer-valued at
integer q). The coefficients are not q-binomials.**

## The conjecture (verbatim from `conjectures/00000001298.md`)

> Definition: Euler's Briot–Bouquet q-difference equations. Conjecture:
> The coefficients of the entire formal solutions of the q-difference
> f(qx) − f(x) = x^k are q-binomials (f-q solution coefficients).

## The refutation

Write f = Σ aₙxⁿ. The equation f(qx) − f(x) = x^k reads
coefficient-wise on x^k as

    a_k · (q^k − 1) = 1,

so the formal solution is **unique**: a_k = 1/(q^k − 1) and aₙ = 0 for
n ≠ k (the n = 0 case is resonant and carries no constraint; the
"entire solution" is the monomial x^k/(q^k − 1)).

For q ≥ 2 and k ≥ 2 the denominator satisfies q^k − 1 ≥ 3, so **no
natural number a_k realizes the forced relation** — the coefficient is
a non-integer rational (kernel-certified: squaring monotonicity gives
q^k ≥ 4, and every positive multiple of a number ≥ 2 exceeds 1). At
the concrete instance q = 2, k = 2 the coefficient is 1/3: no natural
a satisfies 3a = 1.

But every q-binomial coefficient

    [m choose r]_q = Π_{i=1}^{r} (q^{m−r+i} − 1)/(q^i − 1)

is a **polynomial in q with integer coefficients** (classical; e.g.
[3 choose 1]_q = 1 + q + q²), hence an integer at every integer
q ≥ 2 (script: all [m choose r]_q for q ∈ {2,3,4,5}, m ≤ 6 are
integers). A non-integer rational such as 1/3 cannot be a q-binomial
coefficient. The conjectured identification fails.

## Verification

* `reproduce.py` — exact-fraction coefficient-wise solution of the
  q-difference for q ∈ {2,3,4,5}, k ∈ {1,2,3,4}: the unique monomial
  solution x^k/(q^k − 1) satisfies the equation coefficient-wise; the
  coefficient is non-integer for q ≥ 2, k ≥ 2; all q-binomial values
  at integer q are integers; 1/3 is not among the q = 2 values.
* Lean 4 (core, v4.33.1), `lean4/` — the general lemma "no natural
  coefficient realizes (q^k − 1)·a = 1 for q ≥ 2, k ≥ 2" (squaring
  monotonicity), the concrete q = 2, k = 2 instance (3 ∤ 1), the
  denominator anchor 2² − 1 = 3, and the q-binomial anchor
  1 + q + q² = 7 at q = 2. All 5 audited theorems report `does not
  depend on any axioms`.

## Boundary

The kernel certifies the non-integrality of the forced coefficient for
all q ≥ 2, k ≥ 2 and the concrete instance. The coefficient-wise
uniqueness of formal solutions and the polynomiality (integer-valuedness
at integer arguments) of q-binomial coefficients are classical and
cited in prose, with the latter re-verified by the script.
