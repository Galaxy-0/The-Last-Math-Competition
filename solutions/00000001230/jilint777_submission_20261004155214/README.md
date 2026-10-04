# Disproof of conjecture 00000001230

The conjecture says that the Jacobian (sandpile group) of the grid graph `[m₁]×⋯×[mₙ]` is
isomorphic to `⊕_S (ℤ/gcd S)^{e(S)}`, where `S` runs over the subsets of the `mᵢ`. The
exponents `e(S)` are never specified. **No choice of exponents works**, so the conjecture is
false. The second clause ("the 2-dimensional case is given by the K_{m,n} formula and torus
gluing") is too vague to formalize, and we do not need it. Any explicit 2-dimensional formula of
the stated form is just one choice of exponents.

## Counterexample: the 2×2 grid, which is the 4-cycle C₄

- Reduced Laplacian (sink `(0,0)`): `[[2,0,-1],[0,2,-1],[-1,-1,2]]`. It has determinant 4, and
  `Jac(C₄) ≅ ℤ/4`.
- The chip `g = [e₀]` on `(0,1)` has `4g = 0`, because `L̃·(3,1,2) = (4,0,0)`. It also has
  `2g ≠ 0`, because `L̃z = (2,0,0)` forces `2a = 1`.
- For `(m₁,m₂) = (2,2)`, the moduli `gcd S` are `0, 2, 2, 2` (with `ℤ/0 = ℤ`). In any product
  of copies of `ℤ` and `ℤ/2`, `4x = 0` implies `2x = 0`. So `ℤ/4` does not even **embed**
  into such a group.

The counterexample covers all of the following readings at once:

- Path convention: `[m]` is the path with m vertices, or with m edges. In the edge reading
  `C₄ = [1]×[1]` and the moduli are `0, 1`.
- Empty set: `gcd ∅ = 0`, `gcd ∅ = 1`, or ∅ skipped.
- Subsets: subsets of indices or subsets of values.
- Exponents: finite or infinite (the index type in Lean is arbitrary).
- Jacobian: the sandpile group `ℤ^{V∖s}/L̃`, the Baker–Norine `Pic⁰`, or the full `ℤ^V/L`.
- Dimension: `n = 2`, or the claim restricted to `n ≥ 3`. In the second case the cube `[2]³`
  works: `Jac = ℤ/2 ⊕ ℤ/8 ⊕ ℤ/24`, and `[2e₂]` has order 4.

The failure is generic. Smith normal form gives `Jac(2×3) = ℤ/15` and
`Jac(3×3) = ℤ/8 ⊕ ℤ/24`; see the table in the report.

## Contents

- `report.tex`, `report.pdf`: the complete argument and the readings it covers.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) uses a different method. It computes exact Smith
  normal forms of grid Laplacians, then checks for both conventions that the largest invariant
  factor does not divide the lcm of the nonzero moduli. It also re-checks every witness and two
  sanity cases: paths have trivial Jacobian, and the torus remark.
- `verification.txt`: a fresh `lake build` log with the axiom report, the forbidden-token scan
  and the output of `verify.py`.

## Lean

The following are defined from scratch:

- Grid graph: `gridVerts`, `adj` (L¹ distance 1), `lap` and `redLap`, all for an arbitrary list
  `ms`.
- `Coker k M = ℤ^k / Mℤ^k`, a quotient type.
- `Sandpile ms`, `Pic ms`, and `Pic0` (the degree-zero classes of `Pic [2,2]`).
- `ZM d = ℤ/d`, with `ZM 0 = ℤ`.
- `subsetsL` and `gcdL` (`gcd ∅ = 0`).
- `Target ms e = ⊕_S (ℤ/gcd S)^{e(S)}`.
- `IsIso`: an additive bijection.

Main theorems:

- `conjecture_00000001230_false : ¬ ClaimV` (vertex convention)
- `conjecture_00000001230_false_edges : ¬ ClaimE` (edge convention)
- `conjecture_00000001230_false_dim3 : ¬ ClaimV3` (claim restricted to n ≥ 3)
- `no_iso_22`, `no_iso_111_edges`, `no_iso_22_Pic0`, `no_iso_22_Pic`: the explicit failing
  instances.
- `no_injective_hom_C4`, `no_injective_hom_Q3`, `no_injective_hom_PicC4`,
  `no_injective_hom_Pic0C4`: no injective additive map into `∏_{i:ι} ℤ/dᵢ` for any type `ι` and
  any `dᵢ ∈ {0,1,2}`.

Sanity checks:

- `sandpile_C4_iso_Z4` constructs `Jac([2]×[2]) ≅ ℤ/4` via `x ↦ 3x₀+x₁+2x₂ mod 4`. This shows
  that the Lean sandpile group is the right group and that `IsIso` can be satisfied.
- `sandpile_P3_trivial` shows that the conjectured form holds for the path `[3]`, so the
  predicate is not vacuous.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` reports only
`propext` and `Quot.sound`.

Limitations:

- The vague 2-dimensional clause is not formalized.
- The `gcd ∅ = 1` and value-set readings are covered by the strong lemmas, which allow any
  moduli in `{0,1,2}`, rather than by separate `Claim` predicates.
- The torus remark and the table of larger grids are checked only in `verify.py`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想断言：网格图 `[m₁]×⋯×[mₙ]` 的雅可比群（沙堆群）同构于 `⊕_S (ℤ/gcd S)^{e(S)}`，其中 S 取遍 mᵢ 的子集。
指数 e(S) 未给出，我们证明**任何指数选择都不成立**，因此猜想不成立。

反例是 2×2 网格，即 4-圈 C₄。它的约化拉普拉斯矩阵为 `[[2,0,-1],[0,2,-1],[-1,-1,2]]`，雅可比群为 ℤ/4。
顶点 (0,1) 上一个筹码的类 g 满足 4g = 0，但 2g ≠ 0。
而 (m₁,m₂) = (2,2) 时所有模 gcd(S) 只有 0 和 2，在 ℤ 与 ℤ/2 的任意乘积中，4x = 0 必然推出 2x = 0。
因此 ℤ/4 甚至不能单射嵌入这样的群，更不可能同构。

同一个图同时覆盖以下各种理解：
- [m] 表示 m 个顶点的路，或 m 条边的路（后者模为 0 和 1）；
- gcd(∅) 取 0 或 1，或不计空集；
- 子集按下标取或按数值取；
- 指数可以是有限的，也可以是无限的；
- “雅可比群”理解为沙堆群、Baker–Norine 的 Pic⁰，或完整的 ℤ^V/Δℤ^V。

若只考虑 n ≥ 3，可用立方体 [2]³，其雅可比群为 ℤ/2 ⊕ ℤ/8 ⊕ ℤ/24。

Lean 部分（仅核心库）从零定义了网格图、拉普拉斯矩阵、余核商群、沙堆群、ℤ/d 以及猜想中的直和，
并证明了 `¬ ClaimV`、`¬ ClaimE` 和 `¬ ClaimV3`。
作为非空性检验，还显式构造了同构 Jac(C₄) ≅ ℤ/4，并验证路 [3] 满足猜想的形式。
`verify.py` 用 Smith 标准形独立验证了上述结论及更多网格的反例。
