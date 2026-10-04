# Disproof of conjecture 00000007145

The conjecture says that non-Hamiltonian graphs of 4-dimensional polytopes exist,
and that **the minimal dimension of such examples is four**. The minimality clause is false.

**Counterexample.** The rhombic dodecahedron

R = conv{ (±2,0,0), (0,±2,0), (0,0,±2), (±1,±1,±1) } ⊂ ℝ³

is a 3-dimensional polytope with 14 vertices, 24 edges and 12 rhombic facets. Every edge
joins a cube point (±1,±1,±1) to an axis point (±2e_i). So the 8 cube points are pairwise
non-adjacent, and 8 > 14/2. A Hamiltonian cycle would map each cube point injectively to
its successor, which is an axis point, and there are only 6 of those. So the graph has no
Hamiltonian cycle. Because the graph is bipartite with parts of sizes 8 and 6, it has no
Hamiltonian path either. Every polygon has a Hamiltonian graph, so the true minimal
dimension is 3, not 4.

The first clause is true. The pyramid over R (in ℝ⁴) is a 4-polytope whose graph is not
Hamiltonian. The conjecture therefore fails exactly through its minimality clause.

**Readings covered.**
- A point and a segment trivially have no cycle. The formal clause therefore only counts dimensions ≥ 2.
  The counterexample has dimension exactly 3, so it defeats every convention.
- The example is not even traceable, so it also covers the Hamiltonian-path reading (report and `verify.py` only).
- For simple polytopes, Tutte's graph gives a counterexample (cited in the report, not formalized).

## Contents

- `report.tex`, `report.pdf`: the complete argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check (Python 3 standard library). It computes facets by
  brute force, derives vertices and edges from them, and runs an exhaustive search for
  Hamiltonian cycles and paths. It also re-checks the Lean certificate tables.
- `verification.txt`: the fresh build log, the forbidden-token scan and the `verify.py` output.

## Lean

All objects are defined from scratch over integer vectors (`Pt := List Int`).

- **Vertices and edges.**
  - `IsVertex d V p` holds when some functional c ∈ ℤ^d is maximised over V only at p.
  - `Adj d V p q` holds when some functional is maximised exactly at {p, q}, i.e. [p, q] is an edge of conv V.
  - The report proves that integer functionals give the same vertices and edges as real ones for rational polytopes.
- **Dimension.** `FullDim d V` holds when d+1 points of V are affinely independent (a nonzero determinant).
- **Polytopes.** `Polytope` bundles d, a vertex list in ℤ^d without repetitions, a proof that every point is a vertex, and full dimensionality.
- **Hamiltonicity.**
  - `HamCycle d V cyc` means that cyc lists every vertex once, has length ≥ 3, and that cyclically consecutive entries are adjacent.
  - `Polytope.Hamiltonian` means that such a cycle exists.
- **The claim.** `MinDimIsFour` says that a non-Hamiltonian 4-polytope exists and that every non-Hamiltonian polytope of dimension ≥ 2 has dimension ≥ 4.

General lemmas:
- `not_adj_of_cert`: a convex-combination certificate for the midpoint rules out every exposing functional.
- `no_hamCycle`: a set of pairwise non-adjacent vertices containing more than half of all vertices rules out a Hamiltonian cycle.

Results:
- `RD : Polytope` with `RD.d = 3`. `rd_adj_iff` determines the whole graph:
  - the 24 edges come with exposing functionals;
  - the 67 non-edges come with certificates;
  - `rd_cover` shows that the two tables cover all pairs.
- `RD_not_hamiltonian`, `exists_nonHamiltonian_3polytope`.
- **`conjecture_00000007145_false : ¬ MinDimIsFour`**, and `conjecture_00000007145_false'` for the reading without the d ≥ 2 restriction.
- `exists_nonHamiltonian_4polytope`: the pyramid over R. The first clause holds.
- Non-vacuity checks:
  - `Oct_hamiltonian`: the octahedron is a `Polytope` with a Hamiltonian cycle.
  - `oct_nonedge`: `Adj` can fail.

There is no `sorry`, no `native_decide`, and no added axioms. `#print axioms` shows only
`propext`, `Classical.choice` and `Quot.sound`. The build takes about 30 s.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想断言：存在图（1-骨架）非哈密顿的四维多面体，并且这类例子的最小维数是四。后一条（最小维数为四）是错的。

反例是菱形十二面体 R = conv{(±2,0,0),(0,±2,0),(0,0,±2),(±1,±1,±1)}。它是三维多面体，有 14 个顶点、24 条棱、12 个菱形面。
每条棱都连接一个立方体顶点 (±1,±1,±1) 和一个坐标轴顶点。因此 8 个立方体顶点两两不相邻，而 8 > 14/2。
在哈密顿圈中，每个立方体顶点的后继都是互不相同的坐标轴顶点，但坐标轴顶点只有 6 个，矛盾。所以 R 的图不是哈密顿图。
由于二部图两部分大小为 8 和 6，它甚至没有哈密顿路。多边形的图都是哈密顿圈，所以真正的最小维数是 3，不是 4。
第一条是对的：R 上的棱锥是四维多面体，其图也不是哈密顿图。因此猜想恰好在“最小维数为四”这一条上不成立。

Lean 部分（仅用核心库）从零定义了以下对象：整数向量、顶点（某个线性泛函的唯一最大点）、棱（某个线性泛函的最大点集恰为两点）、
满维性（行列式非零）、多面体结构和哈密顿圈。在此基础上，Lean 完整确定了 R 的图：24 条棱都给出暴露泛函，67 个非棱都给出凸组合证书。
Lean 证明了 `conjecture_00000007145_false : ¬ MinDimIsFour`，并验证了四维棱锥的例子和八面体为哈密顿的非空性检查。
报告中还证明了：对有理多面体，整数泛函与实数泛函给出相同的顶点和棱。
`verify.py` 用另一种方法独立复核：暴力求出所有面，由面推出顶点和棱，再穷举搜索哈密顿圈和哈密顿路。
