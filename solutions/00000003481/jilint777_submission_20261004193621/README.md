# Disproof of conjecture 00000003481

A Thue (nonrepetitive) colouring must give every path a colour sequence with no square
factor `xx`. Here "every path" means every sequence of distinct vertices in which consecutive
vertices are adjacent, between any two vertices. The Thue number `π(G)` is the least number of
colours that such a colouring needs.

The conjecture is a conjunction of four clauses:

- **(C1)** the binary tree has `π = 4`;
- **(C2)** the Thue number of general trees is unbounded;
- **(C3)** `π(T) ≤ 2 log Δ(T)` for trees, where `Δ` is the maximum degree;
- **(C4)** this bound is attained asymptotically by subtree families of the complete binary tree.

(C2), (C3) and (C4) are false, so the conjunction is false.

## (C3) is false for every logarithm base `b > 1` (formalised in Lean)

For `b > 1` and `Δ ≥ 1`, `k ≤ 2 log_b Δ` holds iff `b^k ≤ Δ²`. There are three counterexamples:

- **`K₂`, the single edge.** `Δ = 1` and `π = 2`, but `2 log_b 1 = 0`. This works for every base.
- **`P₄`.** `Δ = 2` and `π = 3`. Any 2-colouring of the path contains `aa` or `abab`, and the
  colouring `1 2 3 1` works. Since `3 > 2 log_b 2` for every `b > 4^{1/3} ≈ 1.587`, this rules
  out base 2 (bound `2`), base `e` (bound `1.386`) and base 10 (bound `0.602`), even when
  `Δ ≥ 2` is required.
- **The complete binary tree `B₆` of depth 6.** This is computational, from `verify.py`.
  `Δ = 3` and `π = 4 > 2 log₂ 3 ≈ 3.17`. So the very family named in (C4) violates the bound.

A larger base gives a smaller bound. Refuting every rational base `p/q > 1` therefore refutes
every real base `b > 1`. The rounded-up bound `⌈2 log_b Δ⌉` and the list (choice) version
`π_ch ≥ π` fail on the same examples.

## (C2) and (C4) are false: `π(T) ≤ 4` for every tree (proved in the report)

This is the theorem of Brešar, Grytczuk, Klavžar, Niwczyk and Peterin, *Nonrepetitive
colorings of trees*, Discrete Math. 307 (2007) 163–172. The report gives a complete proof
using only Thue's theorem (1906):

1. Take a square-free word over {1,2,3}.
2. Insert a 4 after every second letter (Kündgen–Pelsmajer). The result is a square-free word in
   which any 3 consecutive letters are distinct.
3. Colour each vertex by the letter indexed by its depth.

Along any path, the depths go down and then up. The "folding lemma" shows that the resulting
colour sequence is square-free.

So the supremum of `π(T)` over all trees is `4`, which makes (C2) false. Since `2 log Δ → ∞`,
the bound is never attained asymptotically. In addition, subtrees of the complete binary tree
have `Δ ≤ 3`, so they cannot form a family with `Δ → ∞`. This makes (C4) false.

## Readings

- **Literal (C3)** (`π ≤ 2 log Δ` for every tree): false for every base. `K₂` refutes it for
  `b > 1`, `P₄` for `b > 1.587`, and `B₆` for `b > √3`.
- **(C3) only "for large Δ" or "up to O(1)":** then (C3) is true but trivial, since `π ≤ 4`.
  But then (C4) and (C2) are false by the cited theorem, whose full proof is in the report but
  not in Lean.
- **(C2):** false for every tree, finite or infinite. Disclosure: the different parameter
  `π_ch`, the nonrepetitive *list* chromatic number, is unbounded on trees (Fiorenzi, Ochem,
  Ossona de Mendez and Zhu 2011). The statement defines colourings, not list colourings.
- **(C1) is not refuted.** By computer we find `π(B_h) = 3` for `2 ≤ h ≤ 5` and `π(B_6) = 4`.
  Hence `π(B_h) = 4` for all `h ≥ 6`, and also for the infinite binary tree. This is consistent
  with (C1).

## Contents

- `report.tex`, `report.pdf`: the complete proofs, the readings, the status of (C1) and the
  references.
- `lean4/`: a Lean 4.19.0 project using only the core library. `Main.lean` defines the
  following from scratch:
  - graphs;
  - paths (all paths, not only root-to-leaf paths);
  - `HasSquare s := ∃ a x b, x ≠ [] ∧ s = a ++ x ++ x ++ b`;
  - Thue colourings, `Colorable` and `IsThueNumber` (unique);
  - trees (simple, connected, with `n-1` edges) and the maximum degree.

  It proves:
  - `thue_K2 : IsThueNumber K2 2` and `thue_P4 : IsThueNumber P4 3`;
  - `K2_tree` and `P4_tree`;
  - **`conjecture_00000003481_false : ∀ p q, q < p → ¬ Claim p q`**, where `Claim p q` is the
    statement "every tree with `Δ ≥ 1` and Thue number `k` has `p^k ≤ Δ² q^k`", i.e.
    `π ≤ 2 log_{p/q} Δ`;
  - `claimCol_false`, the colouring form, which does not use the minimum;
  - `claimDeg2_false`, which shows the `Δ ≥ 2` version fails when `p³ > 4q³`, for example for
    bases 2 and `27/10 < e`;
  - `claim_mono` (a larger base gives a stronger claim) and `nonvacuous`.

  Path enumeration is proved complete by a pigeonhole lemma. The only axioms are `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry` and no `native_decide`.
- `verify.py`: an independent check using only the Python standard library. It:
  - enumerates all colourings and paths to get `π(K₂) = 2` and `π(P₄) = 3`;
  - generates all 987 trees with `n ≤ 12` (the counts match OEIS A000055) and computes `π` for
    each (the maximum is 3);
  - computes `π(B_h)` for `h ≤ 6`, using two different searches for `B₆`;
  - checks the 4-colour depth construction on all 11006 rooted trees with `n ≤ 12` and on
    `B_1, …, B_8`.
- `verification.txt`: the fresh build log, the forbidden-token scan and the output of
  `verify.py`.

**Not in Lean:** the theorem `π(T) ≤ 4`, which needs Thue's infinite square-free word; the
corollaries for (C2) and (C4); the computation `π(B₆) = 4`; and the step from rational to real
bases, a one-line monotonicity argument whose rational form is `claim_mono`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

Thue 染色（非重复染色）要求任意路径的色序列不含平方因子 `xx`。"任意路径"指由互不相同、相邻顶点
依次相连的顶点组成的任意序列，不限于从根到叶的路径。Thue 数 `π(G)` 是这种染色所需的最少颜色数。

猜想由四个子命题合取而成：
- （C1）二叉树的 Thue 数为 4；
- （C2）一般树的 Thue 数无界；
- （C3）对树有 `π(T) ≤ 2 log Δ(T)`，其中 `Δ` 为最大度；
- （C4）该界由完全二叉树的子树族渐近达到。

其中（C2）、（C3）、（C4）均不成立，因此整个合取命题不成立。

**（C3）对任何底数 `b > 1` 都不成立（已在 Lean 中形式化）。** 当 `Δ ≥ 1` 时，`k ≤ 2 log_b Δ` 等价于
`b^k ≤ Δ²`。反例有三个：
- 单边 `K₂`：`Δ = 1`，`π = 2`，而 `2 log_b 1 = 0`，对任何底数都成立；
- 路 `P₄`：`Δ = 2`，`π = 3`。任何 2 染色都含 `aa` 或 `abab`，而 `1 2 3 1` 是合法的 3 染色。
  只要 `b > 4^{1/3} ≈ 1.587`（例如底数 2、e、10）就有 `3 > 2 log_b 2`，即使要求 `Δ ≥ 2` 也是反例；
- 深度为 6 的完全二叉树 `B₆`（由 `verify.py` 计算）：`Δ = 3`，`π = 4 > 2 log₂ 3 ≈ 3.17`。
  可见猜想在（C4）中点名的完全二叉树族本身就违反该界。

底数越大，界越小，所以否定所有有理底数 `p/q > 1` 即否定所有实底数 `b > 1`。向上取整的界
`⌈2 log_b Δ⌉` 以及列表（choice）版本 `π_ch ≥ π` 在同样的例子上也不成立。

**（C2）与（C4）不成立：对每棵树都有 `π(T) ≤ 4`。** 这是 Brešar、Grytczuk、Klavžar、Niwczyk、Peterin
的定理（Discrete Math. 307 (2007) 163–172）。报告中给出了只依赖 Thue 定理（1906）的完整证明：
1. 取三字母无平方字；
2. 每两个字母后插入字母 4（Kündgen–Pelsmajer），得到无平方且任意相邻三个字母互不相同的字；
3. 按顶点深度染色。

沿任意路径，深度先降后升，"折叠引理"保证所得色序列无平方。因此所有树的 `π(T)` 的上确界为 4，
（C2）不成立。由于 `2 log Δ → ∞`，该界不可能被渐近达到；而且完全二叉树的子树满足 `Δ ≤ 3`，
根本不能构成 `Δ → ∞` 的族。因此（C4）也不成立。

**各种解读：**
- 若把（C3）理解为对每棵树成立的上界（字面解读），则对任何底数均不成立：`K₂` 否定 `b > 1`，
  `P₄` 否定 `b > 1.587`，`B₆` 否定 `b > √3`；
- 若把（C3）理解为"对大的 `Δ`"或"相差 O(1)"成立，则由 `π ≤ 4`，它为真但平凡；此时（C4）与（C2）
  由所引定理不成立。该定理的完整证明在报告中，未在 Lean 中形式化；
- （C2）对有限树和无限树都不成立。需要说明：另一个参数 `π_ch`（非重复列表染色数）在树上确实无界
  （Fiorenzi–Ochem–Ossona de Mendez–Zhu 2011），但题目定义的是染色，而不是列表染色；
- （C1）未被否定。计算得 `2 ≤ h ≤ 5` 时 `π(B_h) = 3`，且 `π(B₆) = 4`，从而所有 `h ≥ 6` 以及无限
  二叉树都有 `π = 4`，与（C1）一致。

**Lean（4.19.0，仅核心库）。** `Main.lean` 从零定义了：
- 图；
- 路径（任意路径）；
- 平方因子；
- Thue 染色、`Colorable` 与 `IsThueNumber`（证明了唯一性）；
- 树（简单、连通、`n-1` 条边）以及最大度。

它证明了：
- `π(K₂) = 2` 与 `π(P₄) = 3`；
- 主定理 `conjecture_00000003481_false`：对任何有理底数 `p/q > 1`，命题"每棵树满足 `p^π ≤ Δ² q^π`"
  不成立；
- `claimCol_false`（染色形式）、`claimDeg2_false`（`Δ ≥ 2` 的版本）以及 `claim_mono`。

`π ≤ 4` 的定理、`π(B₆) = 4` 的计算，以及从有理底数到实底数的推广，只在报告和 `verify.py` 中给出。
