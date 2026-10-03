# Disproof of conjecture `00000001749`

**Verdict: FALSE — the degenerate simultaneous Thue system G = 2F with
F(x,y) = xy(x+y) (both forms of degree 3) at a = 195093360, b = 2a has
66 integer solutions (exhaustive divisor enumeration), exceeding the
conjectured bound (deg F)·(deg G) = 3·3 = 9. Ten of them are
kernel-certified by closed evaluation.**

## The conjecture (verbatim from `conjectures/00000001749.md`)

> Definition: Simultaneous Thue equations are systems F(x,y) = a,
> G(x,y) = b of two binary homogeneous forms of degree ≥ 3.
> Conjecture: The number of solutions is at most (deg F)·(deg G); the
> bound is optimal, attained when the composite root structures of F
> and G are of cyclotomic type.

## The refutation

The conjecture quantifies over ALL systems of two degree-≥3 binary
homogeneous forms — including the degenerate pair G = 2F. For
F(x,y) = xy(x+y) and a = 195093360 (= 2⁴·3⁴·5·7·11·17·23, 800
divisors), the system F = a, G = b with b = 2a is equivalent to the
single Thue equation F = a, and exhaustive enumeration over the signed
divisor structure gives **66 integer solutions** — each verified by
direct evaluation of xy(x+y) = a. The conjectured bound is
(deg F)·(deg G) = 3·3 = 9, and 66 > 9: violated by a factor of 7.

The kernel certifies ten of the solutions by closed evaluation
(e.g. (−2448, 33): (−2448)·33·(−2415) = 195093360), their pairwise
distinctness, the degree product 9, and the comparison 9 < 10 ≤ 66.
Since both forms have degree 3 ≥ 3, all of the conjecture's hypotheses
hold while its bound is violated.

## Verification

* `reproduce.py` — exhaustive enumeration: the 800 divisors of a, the
  discriminant test y² + xy − a/x square for each signed divisor, the
  full solution list (66, all re-verified by evaluation), and the
  bound comparison.
* Lean 4 (core, v4.33.1), `lean4/` — ten closed-evaluation solution
  instances, their pairwise distinctness, the degree product
  3·3 = 9, and 9 < 10. All 3 audited theorems report `does not depend
  on any axioms`.

## Boundary

The kernel certifies ten concrete solutions and the bound comparison
(9 < 10), which already refutes the ≤ 9 claim; the exact total 66 is
carried by the script's exhaustive enumeration. The degenerate pair
G = 2F satisfies the conjecture's stated hypotheses (two binary
homogeneous forms of degree ≥ 3); whether the conjecture intended to
exclude proportional forms is not stated and cannot be assumed.
