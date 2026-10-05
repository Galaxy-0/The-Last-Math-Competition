# Disproof of conjecture 00000009898

The conjecture is a conjunction of three clauses:

- **(C1)** The torsion-class lattice `tors A` of a finite-dimensional algebra `A` is distributive
  **if and only if** the oriented path order of the quiver of `A` is a forest order.
- **(C2)** The minimal counterexample to distributivity is the three-vertex oriented cycle.
- **(C3)** "The length of distributive approximations is bounded." This is undefined and not used.

Both (C1) and (C2) are false, so the conjunction is false.

## Counterexample: `A = K(1 → 2)`, over any field `K`

- **Path order.** The path order of `A₂` is the 2-chain `1 < 2`. This is a forest order under
  every definition: down-sets are chains, up-sets are chains, and the Hasse diagram has no cycle.
  It holds for either orientation convention.
- **Indecomposables.** These are `S₁ = (K → 0)`, `S₂ = (0 → K)` and `P₁ = (K --id--> K)`.
- **The lattice is the pentagon N₅.** `tors A` consists of exactly five classes:
  - `0`;
  - `x = {V₂ = 0} = add S₁`;
  - `y = {f surjective} = add{S₁, P₁}`;
  - `z = {V₁ = 0} = add S₂`;
  - `mod A`.

  The order relations are `0 < x < y < mod A` and `0 < z < mod A`.
- **Distributivity fails.** Every representation is an extension
  `0 → S₂^{d₂} → M → S₁^{d₁} → 0`, so `x ∨ z = mod A`. Also `y ∧ z = 0`, and `x ⊆ y`. Hence

  `y ∧ (x ∨ z) = y  ≠  x = (y ∧ x) ∨ (y ∧ z)`,

  and `P₁ ∈ y \ x` witnesses `x ≠ y`. The dual law fails as well:
  `x ∨ (y ∧ z) = x ≠ y = (x ∨ y) ∧ (x ∨ z)`.
- **(C2) fails.** `A₂` has 2 < 3 vertices. One-vertex algebras are local, with `tors = {0, mod A}`,
  so the true minimum is 2.

The following readings are all covered:

- any field;
- any definition of forest order, and either arrow or module convention;
- either distributive law;
- torsion classes with or without the empty class.
- functorially finite torsion classes / support τ-tilting: `KA₂` is representation-finite, so nothing changes;
- the wide-subcategory lattice of the Definition line: for `KA₂` it is the diamond M₃, also non-distributive (report only).

The report also proves the correct criterion: `tors A` is distributive iff the quiver of `A` has
no arrow between distinct vertices. So the "only if" half of (C1) is true, and the "if" half fails
for every quiver with such an arrow.

## Contents

- `report.tex`, `report.pdf`: the complete proof, the readings covered and the correct criterion.
- `lean4/`: a Lean 4.19.0 project, core library only.
- `verify.py`: an independent brute-force check in Python 3 using only the standard library.
  Over `F₂` and `F₃` it:
  - enumerates all representations with `d₁, d₂ ≤ 2`;
  - computes isomorphism classes under `GL × GL` (there are 14);
  - finds quotients by searching for surjective morphisms;
  - finds extensions from the kernels of surjective morphisms;
  - tests all `2^14` subsets for being torsion classes.

  It finds exactly the 5 classes above, forming N₅, and confirms that distributivity fails.
- `verification.txt`: the fresh build log, the axiom report, the forbidden-token scan and the output of
  `verify.py`.

## Lean

Everything is defined from scratch:

- `Fld K`: a field, with all the axioms.
- `Vec K n = Kⁿ`, and linear maps.
- `Rep K`: representations `K^{d₁} --f--> K^{d₂}` of `A₂`, with arbitrary dimensions and any linear `f`.
- `Hom`: morphisms, together with epimorphisms (quotients), `Iso` and `ShortExact`.
- `IsTors`: contains `0` and is closed under quotients and extensions. Closure under isomorphism
  follows (`IsTors.iso_closed`).
- `meet` and `join`: proved to be torsion classes and to be the greatest lower and least upper
  bounds.
- `Quiver`, oriented `Path`, and `ForestOrder`. `ForestOrder` is the strongest reading: a partial
  order in which down-sets and up-sets are chains.

Main theorems, all for an arbitrary field `K`:

- `xC_isTors`, `yC_isTors`, `zC_isTors`, `all_of_S1_S2`, `pentagon`, `a2_forest`.
- `not_distributive K : ¬ Distributive K`, and `not_codistributive K`.
- **`conjecture_00000009898_false K : ¬ IfClause K`**, where
  `IfClause K := ForestOrder A2Q → Distributive K`.
- `iffClause_false` and `minClause_false`, the latter for `MinClause K := A2Q.n < C3Q.n → Distributive K`.
- Non-vacuity:
  - `five_tors`: `0, x, y, z, mod A` are torsion classes, and `{f injective} = add{S₂, P₁}` is not;
  - `Fld` instances for `F₂` (`Bool`) and `F₃`;
  - `conjecture_false_F2` and `conjecture_false_F3`;
  - `c3_facts`.

The project has no `sorry` and no `native_decide`. The only axioms are `propext`, `Quot.sound` and
`Classical.choice`.

Limitations:

- Representations use coordinate spaces `K^d`. Torsion classes are closed under isomorphism, so
  this loses nothing.
- The following are proved in the report only:
  - the equivalence between `KA₂`-modules and representations of `A₂`;
  - the full classification ("exactly five torsion classes"), which `verify.py` also checks for
    `d ≤ 2` over `F₂` and `F₃`;
  - the general criterion.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想由三部分组成：
（C1）有限维代数 A 的 torsion 类格 tors A 为分配格，当且仅当箭图的定向路偏序为森林偏序；
（C2）分配性的极小反例为三顶点定向圈；
（C3）"分配逼近的长度有界"（未定义，本文不需要）。
我们否定（C1）的"⇐"方向，从而否定（C1）本身；同时否定（C2）。因此整个合取命题不成立。

反例：对任意域 K，取 A = K(1 → 2)，即 A₂ 箭图的路代数。
- 其路偏序是两元链 1 < 2。按任何定义它都是森林偏序：下集是链，上集是链，Hasse 图无圈。两种箭头方向约定下均成立。
- 不可分解表示为 S₁ = (K → 0)、S₂ = (0 → K)、P₁ = (K --id--> K)。
- tors A 恰有五个元素：0、x = {V₂ = 0} = add S₁、y = {f 满} = add{S₁, P₁}、z = {V₁ = 0} = add S₂、mod A，构成五边形格 N₅。
- 任一表示都是 S₂^{d₂} 被 S₁^{d₁} 的扩张，故 x ∨ z = mod A；又 y ∧ z = 0，且 x ⊆ y。于是
  y ∧ (x ∨ z) = y ≠ x = (y ∧ x) ∨ (y ∧ z)，其中 P₁ ∈ y \ x 说明 x ≠ y。对偶分配律同样不成立。
- A₂ 只有 2 个顶点，少于 3，所以（C2）也不成立。单顶点代数是局部代数，其 tors = {0, mod A} 是分配格，所以真正的最小顶点数是 2。

报告中还证明了正确的判据：tors A 为分配格，当且仅当箭图中不同顶点之间没有箭头。
因此（C1）的"⇒"方向成立，而"⇐"方向对任何在不同顶点之间有箭头的箭图都不成立。

Lean 部分（4.19.0，仅核心库）从零定义了以下对象：
- 域；
- 线性映射；
- A₂ 的任意维表示，以及态射、满态射（商）、同构、短正合列；
- torsion 类及其格运算（交与并）；
- 箭图的路关系与森林偏序。

主定理 `conjecture_00000009898_false` 对任意域证明了"森林偏序 ⇒ 分配"在 A = KA₂ 上不成立；
`iffClause_false`、`minClause_false` 分别否定"当且仅当"的判据和极小性断言。
非平凡性方面：五个类确实是 torsion 类，而 {f 单} 不是；域的实例取 F₂ 和 F₃。
`verify.py` 用不同的方法独立验证：在 F₂ 和 F₃ 上穷举维数不超过 2 的全部表示，计算同构类、商和扩张，
再检验全部 2^14 个子集，恰好得到五个 torsion 类，构成 N₅，且不满足分配律。
