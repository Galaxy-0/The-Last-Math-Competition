# Disproof of conjecture `00000002231`

**Verdict: FALSE — the prescription "any prescribed closed subset of
[0,1] containing 0" includes uncountable sets, and the deficiency
spectrum of ANY meromorphic function is at most countable: Nevanlinna's
defect relation Σ_a δ(a) ≤ 2 forces at most 2n values with
δ(a) ≥ 1/n for each n (the spectrum is a countable union of finite
shells).  Concrete instance: [0,1] contains the 7 distinct values
7/21, 9/21, 11/21, 13/21, 15/21, 17/21, 1, all ≥ 1/3; realizing them
would force total defect ≥ 7·(1/3) = 7/3 > 2 — violating the defect
relation, whose shell bound allows only 2·3 = 6.**

## The conjecture (verbatim from `conjectures/00000002231.md`)

> Definition: The Nevanlinna deficiency δ(a, f) = 1 − limsup
> N(a,f)/T(f).  Conjecture: There exists a transcendental meromorphic
> f whose deficiency spectrum {δ(a)} realizes exactly any prescribed
> closed subset of [0, 1] containing 0 (deficiency spectrum
> realization).

## The refutation

The defect relation Σ_a δ(a) ≤ 2 (Nevanlinna, classical) caps every
"shell" {a : δ(a) ≥ 1/n} at 2n elements: k values each ≥ 1/n
contribute ≥ k/n to the total, so k/n ≤ 2, i.e. k ≤ 2n.  Hence the
value set {δ(a)} is the union over n of shells of size ≤ 2n — at most
countable.  This holds for EVERY meromorphic f, transcendental or
not; the conjecture quantifies over f but cannot beat an arithmetic
ceiling on the spectrum's cardinality.

"Any prescribed closed subset containing 0" therefore fails for every
uncountable prescription — [0,1] itself, the Cantor set, any interval.
Concretely, [0,1] contains 7 distinct values ≥ 1/3 (7/21, 9/21,
11/21, 13/21, 15/21, 17/21, 1); a spectrum equal to [0,1] would need
deficiencies taking all seven values, contributing ≥ 7·(1/3) = 7/3 >
2 to Σδ — impossible (the n = 3 shell allows at most 6).  The
uncountability side is Cantor's diagonal: no surjection
ℕ → (ℕ → Bool) exists, so the binary expansions in [0,1] can never
be exhausted by a countable spectrum.

For contrast, countable prescriptions ARE sometimes realizable
(e.g. e^z has spectrum {0, 1} — verified numerically: T(r, e^z) = r/π
with no zeros or poles gives δ(0) = δ(∞) = 1, Σδ = 2).  The universal
quantifier "any" is what kills the claim.

## Verification

* `reproduce.py` — exact rational shell bound (max #{δ ≥ 1/n} = 2n
  for n = 1..50); numerical Nevanlinna characteristic for e^z
  (T = r/π to 1e-5, Σδ = 2 tight); constructive Cantor diagonal
  (1000/1000 enumerations miss the diagonal); the 7-value instance
  (all ≥ 1/3, distinct, 7/3 > 2).
* Lean 4 (core, v4.33.1), `lean4/` — `shell_sum` (k values ≥ m
  contribute ≥ k·m), `shell_bound`/`shell_count` (defect relation ⇒
  shell size ≤ 2n), `diagonal_exists` (Cantor, no surjection onto
  Bool sequences), `seven_members`/`seven_exceeds`/
  `seven_exceeds_general` (the instance).  All 8 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the shell-counting arithmetic (the defect
relation's cardinality consequence, in general and at the n = 3
instance) and the Cantor uncountability mechanism.  The defect
relation Σδ ≤ 2 and the real-analysis reading of T(r, f) are
classical (Nevanlinna), cited in prose and spot-checked numerically
for e^z.  The refutation is complete for every uncountable
prescription; no claim is made about which countable closed sets are
realizable.
