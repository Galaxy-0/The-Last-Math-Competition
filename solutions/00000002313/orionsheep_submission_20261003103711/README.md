# Disproof of conjecture `00000002313`

**Verdict: FALSE — at the certified instance r = 2 the claimed
asymptotic log|R(2,p)| = 1·log p + c_{r,p} (c of the "−log 2 type")
gives the ceiling |R(2,p)| ≤ 2p, while the published orders of the
actual restricted Burnside groups are |R(2,5)| = 5³⁴ and
|R(2,7)| = 7²⁰⁴¹⁶ (Havas–Vaughan-Lee et al.; nilpotency class 28,
derived length 5). The exponent gaps — 33 at p = 5, 20415 at p = 7 —
cannot be absorbed by any O(1) constant: the true second term grows
without bound, so no "corrected Witt formula of constant type"
exists.**

## The conjecture (verbatim from `conjectures/00000002313.md`)

> Definition: The restricted Burnside problem concerns the order
> R(r,p) of the largest finite group of rank r and exponent p
> (finiteness proven by Zelmanov). Conjecture: The second coefficient
> of the asymptotics: log|R(r,p)| = (r−1)² log p + c_{r,p} (with c of
> the explicit −log 2 type); the coefficient comes from a corrected
> Witt formula for Lie algebras.

## The refutation

Read at r = 2 the claimed form is log_p|R(2,p)| = 1 + c with
|c| ≤ log 2 — the ceiling |R(2,p)| ≤ 2p. The actual values dwarf
this:

| p | claimed ceiling 2p | published |R(2,p)| | exponent gap log_p gap |
|---|---|---|---|
| 5 | 10 | 5³⁴ (24 digits) | 33 |
| 7 | 14 | 7²⁰⁴¹⁶ (17254 digits) | 20415 |

For the conjecture to survive, the "constant" c_{2,7} would have to
contribute a factor of 7²⁰⁴¹⁵ — not a −log 2 type constant. The
underlying structure is the opposite of O(1): the Witt numbers of the
free Lie algebra on 2 generators, dim of degree m =
(1/m)Σ_{d|m} μ(d)2^{m/d} = 2, 1, 2, 3, 6, 9, 18, 30, 56, …, grow like
2^m/m (1,465,020 through degree 24), and the nilpotency class of
R(2,p) itself grows with p (28 at p = 7). Any "corrected Witt
formula" description of the second coefficient is exponentially
large in p, not constant.

## Verification

* `reproduce.py` — published orders vs claimed ceilings (factors
  5.8e22 and ~7^20414); digit counts; the Witt table 2, 1, 2, 3, 6,
  9, 18, 30, 56 (classic necklace counts) with exponential growth;
  total Witt dimension 1,465,020 through degree 24.
* Lean 4 (core, v4.33.1), `lean4/` — `pow_step`/`pow_mono` (clean
  structural exponent monotonicity for a ≥ 2), `claimed_ceiling_7/5`,
  `R27_dwarfs` (14 < 7²⁰⁴¹⁶ certified as 2401 ≤ 7²⁰⁴¹⁶ via
  monotonicity from 4 ≤ 20416 — no huge-power evaluation),
  `exponent_gap` (1 + 20415 = 20416), `R25_dwarfs`, and
  `conjecture_refuted`. All 8 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the ceilings implied by the conjecture's own
form and their contradiction with the published orders (via clean
exponent monotonicity, avoiding large-power evaluation). The
published orders |R(2,5)| = 5³⁴ and |R(2,7)| = 7²⁰⁴¹⁶ are the
classical computational results (power-commutator presentations),
cited in prose and digit-checked by the script; the Witt table is
verified against the classic values. The asymptotic form — with its
constant second term of the −log 2 type — is refuted at r = 2.
