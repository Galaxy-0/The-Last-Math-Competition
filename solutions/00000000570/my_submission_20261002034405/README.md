# Disproof of TLMC Conjecture 00000000570

**Verdict: FALSE.**

**Conjecture (00000000570).** The Chebyshev-normalized invariant: for every
acyclic cluster algebra, the width of the x-degree support of the Laurent
expansion (in the initial cluster) is at most 2·rank ("locality of degrees").

**中文.** 猜想：任意 acyclic cluster 代数的 Laurent 展开的 x-度支撑集的宽度
≤ 2·rank（度的局部性）。

## Attack (recomputed by hand, matches the recorded attack)

Counterexample: the **Kronecker cluster algebra** — rank 2, exchange matrix
B = [[0, 2], [-2, 0]] (quiver 1 ⇉ 2, affine type Ã₁, acyclic). Cluster
variables expanded in the initial cluster (x₁, x₂) satisfy the rank-2
exchange recurrence

    xₙ₊₁ · xₙ₋₁ = xₙ² + 1        (x₃ = (x₂² + 1)/x₁, alternating mutations)

by the Laurent phenomenon each xₙ is an honest Laurent polynomial in x₁, x₂.
The x₁-exponent of its support spans exactly the interval [-(n-2), n-4]:

| n | terms | x₁-exponent range | width | 2·rank = 4 |
|---|-------|-------------------|-------|------------|
| 3 | 2     | [-1, -1]          | 0     | ok         |
| 4 | 4     | [-2, 0]           | 2     | ok         |
| 5 | 7     | [-3, 1]           | 4     | ok         |
| **6** | 11 | **[-4, 2]**      | **6** | **6 > 4 — violation** |
| 7 | 16    | [-5, 3]           | 8     | violation  |
| 8 | 22    | [-6, 4]           | 10    | violation  |
| 9 | 29    | [-7, 5]           | 12    | violation  |

The widths 0, 2, 4, 6, 8, 10, 12 for x₃ … x₉ match the recorded attack
(`x₆ 宽 6 > 4 = 2·rank 且无界`) exactly. For example:

    x₆ = x₁⁻⁴x₂⁻³ + 4x₁⁻⁴x₂⁻¹ + 6x₁⁻⁴x₂¹ + 4x₁⁻⁴x₂³ + x₁⁻⁴x₂⁵
       + 3x₁⁻²x₂⁻³ + 6x₁⁻²x₂⁻¹ + 3x₁⁻²x₂¹ + 3x₁⁰x₂⁻³ + 2x₁⁰x₂⁻¹ + x₁²x₂⁻³

Both strip endpoints are attained with coefficient 1 (`x₁⁻⁴x₂⁻³` and
`x₁²x₂⁻³`), so the width is exactly 6 > 4. The growth is **unbounded**:
width(xₙ) = 2(n-3), verified by `reproduce.py` up to n = 25 (width 44), with
the inductive mechanism: the leading x₁-exponent of xₙ₊₁ = (xₙ² + 1)/xₙ₋₁ is
twice the top exponent of xₙ minus the bottom exponent of xₙ₋₁, advancing
the interval by one on each side per step. Every other measured spread
(x₂-exponent, x₁x₂-total degree, x₁x₂⁻¹-degree) also grows by 2 per step,
so the disproof does not depend on the choice of width convention.

## Why the numbers are the cluster variables

`reproduce.py` computes x₃ … x₉ by exact greedy Laurent-polynomial division
and verifies each division by remultiplication, and asserts the seven
Laurent-polynomial identities xₙ₋₁·xₙ₊₁ = xₙ² + 1 (n = 2 … 8) exactly. The
Lean side (`lean4/Main.lean`) re-derives the same tables and machine-checks
the same identities coefficientwise. Since ℤ[x₁^±1, x₂^±1] is an integral
domain, the Laurent polynomial q with q·xₙ₋₁ = xₙ² + 1 is unique, so the
verified tables are *the* Laurent expansions of the cluster variables
x₁ … x₉ of the acyclic (Ã₁, rank-2) cluster algebra; width 6 > 2·rank = 4 at
x₆ falsifies the conjecture.

## Boundary of the disproof

* **rank 1**: only one cluster direction; the width is 0 ≤ 2·rank. Holds.
* **rank 2, finite type A₂** (exchange [[0,1],[-1,1]]... i.e. b = 1,
  skew-symmetric finite): `reproduce.py` shows the width stays ≤ 1, well
  under 4. Holds.
* **rank 2, affine Ã₁ (b = 2, this attack)**: fails from x₆ on, unboundedly.
  The Kronecker quiver is acyclic and remains acyclic under mutation, so the
  counterexample is inside the conjecture's hypothesis.
* **rank R ≥ 3 acyclic**: the direct product Kronecker × A₁^{R-2} is acyclic
  of rank R, and the product Laurent expansion has the same support widths
  as the Kronecker factor (the extra A₁ factors only contribute monomial
  shifts), so x₇ (width 8), x₉ (width 12), … violate 2·rank for every R ≥ 2.
* **Chebyshev normalization**: the rank-2 Chebyshev normalization rescales
  each cluster variable by a Laurent *monomial*; a monomial shift translates
  the whole support uniformly, leaving every width invariant. The attack
  survives normalization.

## Lean 4 verification (core Lean, no Mathlib, zero axioms, zero `sorry`)

`lean4/Main.lean` proves, with `decide` only on closed propositions:

* `relz2 … relz8` — all seven exchange relations xₙ₋₁·xₙ₊₁ = xₙ² + 1 hold
  coefficientwise for the tables `TBL1 … TBL9` (assembler `rel_of_keys`);
* `width3 … width9` — the support of xₙ lies in the x₁-strip [-(n-2), n-4],
  with both endpoints attained (nonzero coefficients), so the widths are
  exactly 0, 2, 4, 6, 8, 10, 12;
* `disproof_00000000570` — packages the chain with the violations
  width(x₆) = 6 > 2·2 = 4 and width(x₉) = 12 > 4.

`lean4/Check.lean` prints `#print axioms` for every declaration; all report
"does not depend on any axioms". Build:

    cd lean4
    lake build
    lake env lean Check.lean

## Reproduction

    python3 reproduce.py

Recomputes x₃ … x₂₅ from scratch (pure Python, no dependencies), verifies
every division by remultiplication, asserts the seven exchange identities
exactly, prints the width table (0, 2, 4, …, 44), the boundary comparison
b = 1 (finite A₂, widths ≤ 1), and the Lean term tables for x₃ … x₉.
