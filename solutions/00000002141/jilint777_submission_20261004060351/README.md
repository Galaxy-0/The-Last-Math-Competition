# Counterexample to conjecture 00000002141

The conjecture says that the minimal order of a cospectral regular pair is 10, and that
**the cospectral regular pair of order 10 is unique**. The uniqueness clause is false.

Two different cospectral pairs of 4-regular graphs on 10 vertices:

| pair | graphs (graph6) | characteristic polynomial |
|---|---|---|
| 1 | `` ICR`vGyu? ``, `` ICR`tjWY_ `` | x¹⁰ − 20x⁸ − 16x⁷ + 110x⁶ + 136x⁵ − 180x⁴ − 320x³ + 9x² + 200x + 80 |
| 2 | `` ICR`uiwY_ ``, `ICdedhkY_` | x¹⁰ − 20x⁸ − 14x⁷ + 108x⁶ + 104x⁵ − 183x⁴ − 188x³ + 80x² + 68x − 16 |

Within each pair the graphs are non-isomorphic. The pairs have different spectra, and
`A1` is isomorphic to neither graph of pair 2. Both pairs are 4-regular, so they are not
complements of each other. All four graphs are connected; 2K₅ is the only disconnected
4-regular graph on 10 vertices, and it has no cospectral mate. A full enumeration with nauty shows that order 10 has exactly
two 4-regular cospectral pairs (these) plus their two 5-regular complements, and that no
cospectral regular pair has fewer than 10 vertices.

Non-isomorphism uses two isomorphism invariants:

- **(P)** some edge lies in no triangle. This holds for B1, A2 and B2, but not for A1.
- **(Q)** some triangle-free edge shares no endpoint with another one. This holds for A2 but not for B2.

## Contents

- `report.tex`, `report.pdf`: the complete argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library; uses `nauty-geng` for the enumeration if installed)
  checks three things:
  - the exact characteristic polynomials, computed two ways;
  - an exhaustive isomorphism search;
  - the full enumeration of regular graphs on at most 10 vertices.
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

- `Cospectral g h` means equal numbers of closed walks `tr(A^k)` for all `k ≤ 10`. By
  Newton's identities this is equivalent to equal spectra on 10 vertices.
- Two further certificates of cospectrality do not rely on Newton's identities:
  - `orth_1` and `orth_2` give integer matrices `M` with `M·Mᵀ = 4I` and `M·A = B·M`, so
    `B = (M/2) A (M/2)ᵀ` is an orthogonal similarity (a Godsil–McKay switching on `{0,4,5,6}`
    followed by a relabelling).
  - `cp_A1`, `cp_B1`, `cp_A2` and `cp_B2` compute the characteristic polynomial coefficients.
- `Iso` is the existence of a bijection that preserves adjacency. `iso_hasNT` and
  `iso_hasIsolatedNT` prove that (P) and (Q) are isomorphism invariants.
- `pair_1` and `pair_2` show that both are cospectral regular pairs.
- `conjecture_00000002141_false : ¬ UniquePair`, and
  `conjecture_00000002141_conjunction_false : ¬ (MinOrder10 ∧ UniquePair)` holds for any first clause.
- Sanity checks: `iso_refl` and `iso_A1_A1r` (a nontrivial relabelling) show that `Iso` is not vacuous.

The project has no `sorry`, no `native_decide`, and no added axioms.
`#print axioms` shows at most `propext` and `Quot.sound`. The certificates use no axioms.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称同谱正则图对的最小阶为 10，并且 10 阶的同谱正则图对唯一。唯一性这一条是错的。
我们给出两对互不相同的 10 阶 4-正则同谱图：每对内部的两个图不同构，两对之间特征多项式不同，
并且第一对的图与第二对的任何图都不同构。
用 nauty 穷举可知：10 阶恰有两对 4-正则同谱图，以及它们补图构成的两对 5-正则同谱图；10 阶以下没有同谱正则图对。
Lean 用闭途径数 tr(A^k)（k ≤ 10）刻画同谱，并用两个同构不变量证明了不同构。
