# Disproof of conjecture 00000001289

The conjecture says that the "nim graph" `Q_⊕(n)` of the hypercube has **diameter `2^n − 1`
and chromatic number `2^n`**. Its vertices are the `2^n` vertices of the `n`-cube, and its
edges are "given by ⊕". This is false for every `n ≥ 2`, **whatever edge set is meant**.

**Key fact.** A simple graph on `N` vertices with chromatic number `N` is complete. If `u` and
`v` were non-adjacent, `v` could reuse the colour of `u`, and `N − 1` colours would suffice.
A complete graph has diameter `1`. So for `N ≥ 3` no graph has `χ = N` and `diam = N − 1`.
With `N = 2^n` the clause fails for all `n ≥ 2`, first at `n = 2`, where `χ = 4` forces `K_4`,
whose diameter is `1 ≠ 3`.

Actual values under the two natural readings (`u ⊕ v` is bitwise XOR):

| reading | rule | χ | diam | claimed (χ, diam) |
|---|---|---|---|---|
| (H) hypercube `Q_n` | `u ⊕ v` is a power of 2 | 2 | n | (2^n, 2^n − 1) |
| (K) complete `K_{2^n}` | `u ⊕ v ≠ 0` | 2^n | 1 | (2^n, 2^n − 1) |

At `n = 1` both readings give `K_2`, and the clause holds there (diameter 1, χ = 2). So the
predicates are not vacuous.

Scope and robustness:

- Every rule that depends only on `u ⊕ v` is symmetric. A loop would make proper colouring
  impossible. So `Q_⊕(n)` is a simple graph, and the Lean theorem covers all of them.
- A disconnected graph has infinite diameter.
- In the report and `verify.py` only (not in Lean):
  - `χ + diam ≤ N + 1` for every connected graph, so other vertex counts are also excluded
    up to `N < 2^{n+1} − 2`;
  - acyclic (game-graph) directed readings give infinite directed diameter.

## Contents

- `report.tex`, `report.pdf`: the complete argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) is an independent brute-force check using BFS and
  colouring search. It covers:
  - all 64 graphs on 4 vertices;
  - `χ = N ⇒ complete` and `χ + diam ≤ N + 1` on all graphs with 3 to 6 vertices;
  - readings (H) and (K) for `n ≤ 5`;
  - all Cayley graphs `Cay((Z/2)^n, S)` for `n = 2, 3`;
  - the directed remark.
- `verification.txt`: fresh build log, forbidden-token scan, and the `verify.py` output.

## Lean

All objects are defined from scratch:

- graphs are `Nat → Nat → Bool` on `{0, …, N−1}`;
- `IsSimple`, `IsProperColoring`, `Colorable`, `ChromaticNumberEq` (least number of colours);
- `WalkFrom` (explicit walks), `WalkLe` (distance ≤ k), `DistEq`, `DiameterEq`;
- `reach_iff` proves the executable `reach` equivalent to `WalkLe`.

Main results:

- `adj_of_chromatic`: `χ = N` implies the graph is complete.
- `no_graph_diam_chi`: `∀ N ≥ 3, ∀ G` simple on `N` vertices, `¬ (diam G = N − 1 ∧ χ G = N)`.
- `claimAt_false`: for every `n ≥ 2`, no simple graph on `2^n` vertices satisfies the clause.
- **`conjecture_00000001289_false (Q) (hQ : IsSimple (Q 2) (2^2)) : ¬ NimClaim Q`**, where
  `NimClaim Q := ∀ n ≥ 1, diam (Q n) = 2^n − 1 ∧ χ (Q n) = 2^n`.
- Concrete readings, both defined with XOR `^^^`:
  - `hypercube2_chi`, `hypercube3_chi` (χ = 2);
  - `hypercube2_diam`, `hypercube3_diam` (diameter 2, 3);
  - `nimComplete_chi` (χ = N for all N, via `pigeonhole`) and `nimComplete_diam` (diameter 1);
  - `hypercube_reading_false`, `complete_reading_false`.
- Non-vacuity:
  - `claimAt_one`: the clause holds at n = 1;
  - `nonvacuous_four`: the path P₄ has diameter 3, and K₄ has χ = 4.
- `all_masks_fail`: an independent `decide` cross-check over all 64 labelled graphs on 4 vertices.

The project has no `sorry`, no `native_decide`, and no added axioms. `#print axioms` shows only
`propext`, `Quot.sound` and, for the general theorems, `Classical.choice`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称超立方体的 nim 图 `Q_⊕(n)`（顶点为 n 维立方体的 `2^n` 个顶点，边由 ⊕ 给出）的直径为
`2^n − 1`，色数为 `2^n`。对每个 `n ≥ 2` 这都是错的，而且与边集的具体定义无关。

关键事实：`N` 个顶点的简单图若色数为 `N`，则必为完全图。否则，若 `u`、`v` 不相邻，可让 `v` 使用
`u` 的颜色，`N − 1` 种颜色就够了。完全图的直径为 1。因此 `N ≥ 3` 时不存在色数为 `N` 且直径为
`N − 1` 的图。取 `N = 2^n`，猜想对所有 `n ≥ 2` 都不成立。最小反例是 `n = 2`：色数 4 迫使图为
`K_4`，其直径为 1 而不是 3。

两种自然解读的真实取值：
- 超立方体解读（`u ⊕ v` 为 2 的幂）：色数 2，直径 n。
- 完全图解读（`u ⊕ v ≠ 0`）：色数 `2^n`，直径 1。

`n = 1` 时猜想成立（`K_2`），说明谓词并非空洞。

Lean（4.19.0，仅核心库）从零定义了以下概念：
- 简单图、正常着色、色数；
- 途径、距离、直径。

在此基础上，Lean 对所有边集证明了一般定理和 `conjecture_00000001289_false`，计算了两种具体解读，
并用 `decide` 对 4 个顶点上的全部 64 个图做了独立验证。`verify.py` 用 BFS 和着色搜索做了独立的
穷举检验。

以下内容只在报告和 `verify.py` 中处理，未在 Lean 中形式化：
- 不同顶点数的情形（`χ + diam ≤ N + 1`）；
- 有向图解读。
