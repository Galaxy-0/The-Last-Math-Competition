# Disproof of conjecture 00000001090

The conjecture says that the maximal order of the automorphism group of an **MDS code
over GF(3) of type [12,6]** is 660, attained by an M₁₁ embedding, and that the orders for
all other equivalence classes divide 132.

**There is no MDS code over GF(3) of type [12,6].** An MDS [12,6] code has minimum
distance 12 − 6 + 1 = 7, and no ternary [12,6,7] code exists. So no code attains the
order 660, and the first clause ("the maximum is 660, attained") is false. This holds for
any notion of automorphism group: permutation, monomial or full. The other clauses are
vacuously true, and we make no claim about them.

## The argument

**Theorem.** Let k ≥ 2 and let G be a k × n matrix over F₃ in which every nonzero
combination of the rows has weight ≥ n − k + 1. Then n ≤ k + 2.

This is the q = 3 case of the classical bound n ≤ q + k − 1 for MDS codes. The proof:

1. **Two codewords.** Linear algebra gives two independent messages whose codewords
   u and v vanish on the first k − 2 coordinates.
2. **Lower bound.** The 8 nonzero combinations au + bv are nonzero codewords. Their
   weights therefore sum to at least 8(n − k + 1).
3. **Upper bound.** Each of the remaining n − k + 2 coordinates is nonzero in either
   0 or 6 of these 8 combinations. So the sum is at most 6(n − k + 2).
4. **Conclusion.** The two bounds together force n ≤ k + 2.

For [12,6], at most 8 · 6 = 48 is available, but 8 · 7 = 56 is needed. The Griesmer
bound (n ≥ 14) gives a second proof.

## Readings covered

- **Automorphism group.** The notion does not matter. Lean refutes the conjecture
  for both PAut and MAut, and shows that no MDS [12,6] code has *any* property P.
- **Definition of MDS.** Only d ≥ 7 is used, so d = 7 and d ≥ 7 are both covered.
- **"[12,6]" as [n, d].** An MDS code would then be a [12,7,6] code, which also does
  not exist.
- **"MDS" dropped (all ternary [12,6] codes).** The claim is still false. The
  repeated-pair code {(x₀,x₀,…,x₅,x₅)} has 2⁶ · 6! = 46080 > 660 permutation
  automorphisms:
  - Lean exhibits 768 distinct ones.
  - `verify.py` checks all 46080.
- **Golay reading** (probably what was meant). The conjecture's group is the stabilizer
  of the *permutation* equivalence class, i.e. PAut, not the monomial group.
  - Up to monomial equivalence the ternary Golay code is the unique [12,6,6]₃ code
    (Pless 1968; Delsarte–Goethals 1975).
  - Its monomial class splits into exactly **5 permutation classes**, with
    |PAut| = 108, 120, 432, 660 and 7920 (`verify.py`).
  - The generator matrix `golay` = [I₆ | A] has |PAut| = 660.
  - Doubling its column 6 gives `golay'`, with |PAut| = 7920 = |M₁₁|.
  - So the maximum is 7920, not 660. The M₁₁ in the statement is actually attained as
    a full PAut, and 660 = |PSL(2,11)| is not the maximum.
  - The orders 108, 120 and 432 do not divide 132, so the "other classes" clause fails
    too.
  - Lean proves that `golay'` is a [12,6,6] code with at least 720 > 660 distinct
    permutation automorphisms.

## Contents

- `report.tex`, `report.pdf`: the complete argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using the Python 3 standard library.
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

**Definitions**

- `F3 = Fin 3`. Codes are given by generator matrices.
- Code notions: `comb`, `codeword`, `wt`, `IsGenMatrix` (independent rows),
  `InCode`, `MinDistGe`, `HasMinDist`, and `IsMDS n k G` (independent rows and
  minimum distance exactly n − k + 1).
- Automorphisms: `IsPAut` and `IsMAut`, with group orders `PAutOrder` and `MAutOrder`.

**Theorems**

- `dep`: linear dependence of k > r vectors in F₃ʳ.
- `no_mds_ternary`: the theorem above, proved for all n and k.
- `no_mds_12_6`, `no_dist7_12_6` and `no_mds_12_7`.
- `no_mds_12_6_with P`: no MDS [12,6] code has property P, for any P.
- `conjecture_00000001090_false : ¬ Conjecture1090`, where `Conjecture1090` is the
  conjunction of the three clauses for PAut.
- `conjecture_00000001090_monomial_false`: the same for MAut.

**Non-vacuity**

- `tetra_mds`: the tetracode is a [4,2,3] MDS code, so the bound n ≤ k + 2 is sharp.
- `golay_12_6_6`: the Golay code is a [12,6] code with minimum distance exactly 6.

**Golay reading**

- `golay'_12_6_6`: `golay'` is a [12,6] code with minimum distance exactly 6.
- `golayAuts_aut` and `golayAuts_nodup`: 720 distinct permutation automorphisms.
  They are the products h ∘ k, where:
  - h ranges over 30 automorphisms with distinct images of (0,1);
  - k ranges over 24 automorphisms fixing 0 and 1.
  Each of these 54 permutations is checked by `decide +kernel` (`RowsOK`,
  `paut_of_rows`), and products of automorphisms are automorphisms (`autCore_comp`).
- `golay_reading_witness`: some [12,6,6] code has more than 660 distinct
  permutation automorphisms.
- `golay_reading_false : ¬ GolayMax660`.
- `golay'_order_ge`: the PAut order of `golay'` is at least 720.
- The exact orders 660 and 7920, and the five-class spectrum, are checked in
  `verify.py` only.

**"MDS" dropped**

- `atMost660_false`: some [12,6] code has more than 660 distinct permutation
  automorphisms.
- `pair_order_ge`: the PAut order of the pair code is at least 768.

**Axioms**

- There is no `sorry`, no `native_decide` and no added axiom.
- The MDS results use only `propext` and `Quot.sound`.
- The automorphism-list results (pair code and Golay reading) may also use
  `Classical.choice`, through core list lemmas.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想：GF(3) 上 [12,6] 型 MDS 码的自同构群阶的最大值为 660（由 M₁₁ 的嵌入取得），其他等价类的群阶都整除 132。

**结论：GF(3) 上不存在 [12,6] 型 MDS 码。** 这样的码最小距离应为 7，即 [12,6,7]₃ 码，但它不存在。
因此没有任何码的自同构群阶为 660，"最大值 660 且可取到"这一条不成立，猜想为假。
这个结论与自同构群取置换群、单项群还是全自同构群无关。其余两条在空集上平凡成立，我们不对它们作任何断言。

**一般定理：** 设 k ≥ 2。若 F₃ 上 k × n 矩阵的行的每个非零线性组合的重量都 ≥ n − k + 1，则 n ≤ k + 2。证明分三步：

1. 由线性相关性，取两个独立的消息，使对应码字 u、v 在前 k − 2 个坐标上为 0。
2. au + bv 的 8 个非零组合都是非零码字，重量之和至少为 8(n − k + 1)。
3. 其余每个坐标恰在 0 个或 6 个组合中非零，所以重量之和至多为 6(n − k + 2)。

两者矛盾，除非 n ≤ k + 2。

**其他读法：**

- **Golay 码读法**（作者大概想说的是这个）。猜想定义的群是置换等价类的稳定群，即置换自同构群 PAut，而不是单项自同构群。
  - 在单项等价意义下，三元 Golay 码是唯一的 [12,6,6]₃ 码（Pless 1968；Delsarte–Goethals 1975）。
  - 它的单项等价类恰好分裂成 5 个置换等价类，PAut 的阶分别为 108、120、432、660、7920（由 verify.py 验证）。
  - 生成矩阵 `golay` 的 PAut 阶为 660；把它的第 6 列乘以 2 得到 `golay'`，其 PAut 阶为 7920 = |M₁₁|。
  - 因此最大值是 7920 而不是 660；而 108、120、432 都不整除 132，"其余类整除 132"这一条也不成立。
  - Lean 证明了 `golay'` 是 [12,6,6] 码，并给出了它的 720 > 660 个互不相同的置换自同构。

- 若把 [12,6] 读作 [n,d]，则对应的 MDS 码是 [12,7,6]₃，同样不存在。
- 若去掉"MDS"，命题仍然为假：重复对码 {(x₀,x₀,…,x₅,x₅)} 是 [12,6] 码，置换自同构群阶为 2⁶·6! = 46080 > 660。Lean 中给出了其中 768 个互不相同的自同构。

**Lean 部分**（仅用核心库）形式化了码、重量、最小距离、MDS 和自同构群，证明了上述一般定理及 `¬ Conjecture1090`。
还验证了四元码（tetracode）是 [4,2,3] MDS 码、Golay 码是 [12,6,6] 码，以说明这些定义非空。

**verify.py** 用不同方法独立验证：
- 穷举说明 [8,2,7]₃ 码不存在，并计算 Griesmer 界；
- 穷举检查重复对码的全部 46080 个自同构；
- 完整计算 Golay 码单项等价类中 5 个置换等价类的 PAut 阶，确认 |PAut(golay')| = 7920。
