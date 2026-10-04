# Disproof of conjecture 00000008556

The conjecture makes three claims about the free distributive lattice `FD(n)` on `n` generators:

1. `Aut(FD(n))` is the symmetric group;
2. its fixed-point lattice is "of partition-symmetric type";
3. **the maximal chain length of the fixed-point lattice is exactly `log p(n)`**.

The third claim is false for every base of the logarithm, so the conjunction is false. Claim 2
is undefined, and the disproof does not need it.

## Counterexample: n = 1, 2, 3

- `FD(n)` is the set of nonconstant monotone Boolean functions in `n` variables. Equivalently,
  it is the closure of the projections under `∧` and `∨`. Its sizes are 1, 4, 18, 166.
- The automorphisms are the permutations of the variables, so claim 1 is true. The elements they
  fix are the threshold functions `T_k = [at least k of the n variables]`, `1 ≤ k ≤ n`.
- These form the chain `T_n < … < T_1`, of length `ℓ(n) = n − 1`.

| n | ℓ(n) | p(n) | `ℓ(n) = log_b p(n)` means |
|---|---|---|---|
| 1 | 0 | 1 | `b⁰ = 1` (always true) |
| 2 | 1 | 2 | `b = 2` |
| 3 | 2 | 3 | `b² = 3`, but `b = 2` gives `b² = 4` |

So no base `b` works. The natural logarithm fails already at `n = 2`, since `1 ≠ ln 2`.

The counterexample covers all of the following readings at once:

- Chain length counted in steps or in elements (lengths shift by 1).
- The free lattice, or the free **bounded** distributive lattice with 0 and 1 adjoined. In the
  bounded lattice the thresholds run over `0 ≤ k ≤ n+1` and the lengths are `n+1`.
- Any base: `e`, 2, 10, or even `0 < b < 1`.
  In each of the four readings the lengths at `n = 1, 2, 3` are consecutive integers
  `s, s+1, s+2`. Then `b^s = 1` and `b^(s+1) = 2` force `b = 2`, and `b^(s+2) = 4 ≠ 3`.
- Fixed points of the full automorphism group, or of `S_n`. Under claim 1 these are the same.
  If claim 1 were false, the conjunction would already be false.
- Any notion of "fixed-point lattice" at all, as long as chain lengths are integers:
  `b^L₂ = 2` and `b^L₃ = 3` give `2^L₃ = 3^L₂`, so `L₂ = L₃ = 0`, but `b⁰ ≠ 2`.
- Rounded logarithms (floor, ceiling or nearest, bases 2, e, 10): each fails at some `n ≤ 5`.
- The identity holding only for large `n` (report only): `log p(n) = o(n)`, while `ℓ(n) = n − 1`.

## Contents

- `report.tex`, `report.pdf`: the complete argument and the readings it covers.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) is an independent check that uses a different
  representation (sets of true points). For `n ≤ 4` and both lattices it checks:
  - `FD(n)` computed as a closure, compared with the set of monotone functions;
  - `Aut(FD(n))` computed with no assumptions: brute-force backtracking over lattice
    automorphisms for `n ≤ 3`, and automorphisms of the join-irreducible poset for `n = 4`.
    The result is `S_n` in every case;
  - the fixed points of the full group, and their longest chain;
  - `p(n)` by Euler's pentagonal recurrence, cross-checked by enumeration;
  - every logarithm reading above.
- `verification.txt`: a fresh `lake build` log with the axiom report, the forbidden-token scan
  and the output of `verify.py`.

## Lean

The following are defined from scratch. Truth tables are encoded as natural numbers
`f < 2^(2^n)`.

- `Gen n bnd`: the inductive `∧`/`∨`-closure of the projections (with 0 and 1 if `bnd`).
- `FDset n bnd`: monotone truth tables, nonconstant unless `bnd`.
- `IsPerm`, `act`: the `S_n` action. `Fixed`: the `S_n`-fixed elements.
- `IsAut`: lattice automorphisms of `FD(n)`. `AutIsSym`: claim 1. `FixedAut`: the elements fixed
  by every automorphism.
- `MaxChainLen`, `threshold`, `IsPartition`, `partitionsL`, `p`.
- `NumSys`: any type with an associative unital multiplication and an injective multiplicative
  cast of `ℕ`, such as `ℕ, ℤ, ℚ, ℝ, ℂ`. `IsLog R b x y :⇔ b^y = x`; for a real base this is the
  definition of `y = log_b x`.

Main theorems:

- `fd_spec`: for `1 ≤ n ≤ 3`, `Gen = FDset`, and both equal an explicit list.
  `fd_sizes` gives the sizes 1, 4, 18 and, bounded, 3, 6, 20.
- `fixed_iff_thr`: for `1 ≤ n ≤ 3`, the fixed elements are exactly the thresholds.
- `maxChain_fixed`: the maximal chain lengths are 0, 1, 2 (free) and 2, 3, 4 (bounded).
- `act_isAut`: every variable permutation is an automorphism.
  `fixedAut_iff`: under claim 1, `FixedAut = Fixed`.
- `mem_partitionsL` (for all `n`) and `p_values`: `p(1..5) = 1, 2, 3, 5, 7`.
- `logClause_false : ¬ LogClause R bnd elems`, for every number system, both lattices and both
  length conventions.
- **`conjecture_00000008556_false : ¬ Conjecture R C2 bnd elems`**. Here `Conjecture` is claim 1
  ∧ an arbitrary predicate `C2` ∧ claim 3 stated for `FixedAut`.
- `no_lengths_fit`: no integers `L₂, L₃` and no base `b` satisfy `b^L₂ = p(2)` and
  `b^L₃ = p(3)`.
- Non-vacuity:
  - `natSys` and `intSys` are number systems;
  - `act_isAut` shows that `IsAut` is satisfiable;
  - `clause_holds_n_le_2` shows that the clause does hold for `n ≤ 2` with `b = 2`, so the
    failure is genuinely at `n = 3`.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` reports at most
`propext` and `Quot.sound`.

Limitations:

- Core Lean has no reals, so the base ranges over an abstract `NumSys`, of which `ℝ` is an
  instance.
- The following are proved in the report only: the general-`n` statements (`FD(n)` = monotone
  functions; fixed points = thresholds), the truth of claim 1 (`Aut = S_n`, also brute-forced in
  `verify.py` for `n ≤ 4`), and the asymptotic remark. Lean covers `n ≤ 3`, which is all the
  disproof needs.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想对 n 个生成元的自由分配格 FD(n) 断言三件事：
（1）其自同构群为对称群；（2）不动点格为"分拆对称型"；（3）不动点格的极大链长恰为 log p(n)。
第（3）条对任何对数底都不成立，因此整个合取命题不成立。第（2）条没有定义，证明中不需要它。

FD(n) 是 n 元非常值单调布尔函数全体，即投影在 ∧、∨ 下的闭包，元素个数为 1、4、18、166。
它的自同构恰为变量置换，所以第（1）条成立。被所有自同构固定的元素恰为阈值函数
T_k =「n 个变量中至少 k 个为真」，1 ≤ k ≤ n。它们构成长度为 n − 1 的链。

于是 n = 1、2、3 时链长为 0、1、2，而 p(n) = 1、2、3。
由 log_b 2 = 1 得 b = 2，但 log_2 3 ≠ 2，所以不存在合适的底；自然对数在 n = 2 时已不成立（1 ≠ ln 2）。

同一反例同时覆盖以下理解：
- 链长按边数或按元素个数计算；
- 自由格，或添加 0、1 后的有界自由分配格（此时链长为 n + 1）；
- 任意的底，包括 e、2、10 以及 0 < b < 1：四种理解下 n = 1、2、3 的链长都是相邻整数 s、s+1、s+2，
  由 b^s = 1、b^(s+1) = 2 得 b = 2，再由 b^(s+2) = 4 ≠ 3 得出矛盾；
- 不动点取全自同构群的，或取 S_n 的（在第（1）条之下两者相同；若第（1）条不成立，合取已不成立）；
- 对"不动点格"的任何理解，只要链长是整数：由 b^L₂ = 2、b^L₃ = 3 得 2^L₃ = 3^L₂，
  只能 L₂ = L₃ = 0，而 b⁰ ≠ 2；
- 取整后的对数（下取整、上取整、四舍五入，底为 2、e、10）：都在某个 n ≤ 5 处不成立；
- 只对充分大的 n 成立的理解（仅在报告中）：log p(n) = o(n)，而链长为 n − 1。

Lean 部分（仅核心库）从零定义了以下对象：
- 自由分配格：既定义为投影的 ∧/∨ 闭包，也定义为单调函数集，并对 n ≤ 3 证明两者相同；
- 变量置换作用、格自同构、不动点、链长和分拆数；
- 对数：以 b^y = x 刻画，底取自任意"数系"（ℕ、ℤ、ℚ、ℝ、ℂ 均满足其公理）。

主定理 `conjecture_00000008556_false` 否定了第（1）条 ∧ 任意第（2）条 ∧ 第（3）条（对全自同构群的不动点）。
`verify.py` 用不同的表示独立验证上述结论，包括对 n ≤ 4 用回溯穷举全部自同构。
