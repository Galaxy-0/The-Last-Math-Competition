# Counterexample to conjecture 00000000438

The conjecture says that the primitive Lie algebra of the Hopf algebra **Sym** of
noncommutative symmetric functions (NSym) has `n`-th homogeneous dimension equal to the
Eulerian number `A(n,1)`. It also says this algebra is isomorphic to a "generalized Lie
n-algebra", which the statement never defines. A graded isomorphism preserves homogeneous
dimensions, so the conjecture implies

    dim Prim(NSym)_n = A(n,1)   for all n ≥ 1.

This dimension clause is false at `n = 3`. We never need the undefined isomorphism part.

NSym is the free algebra on `S_1, S_2, …` with `Δ S_k = Σ_{i+j=k} S_i ⊗ S_j`
(`S_0 = 1`). Its degree-3 part has basis `S_3, S_21, S_12, S_111`. Write
`Δ̄x = Δx − x⊗1 − 1⊗x`. Then

```
Δ̄(a S_3 + b S_21 + c S_12 + d S_111)
   = (a+b+c)(S_2⊗S_1 + S_1⊗S_2) + (b+c+3d)(S_11⊗S_1 + S_1⊗S_11),
```

so the primitives form the 2-dimensional space `{a+b+c = 0, b+c+3d = 0}`. A basis is
`Ψ_3 = 3S_3 − S_21 − 2S_12 + S_111` and `[S_2,S_1] = S_21 − S_12`. This holds over every
field, and over ℤ the module is free of rank 2.

`A(3,1)` is not 2 under any convention:

- permutations of {1,2,3} with exactly one descent (or ascent): `A(3,1) = 4`;
- 1-based convention (OEIS A008292, `k` ascending runs): `A(3,1) = 1`.

In fact `A(m,1)` is either `2^m − m − 1` (values 0, 1, 4, 11, …) or `1`, so it never
equals 2, and no shift of the index rescues the formula.

For `n = 1..10` the primitive dimensions are 1, 1, 2, 3, 6, 9, 18, 30, 56, 99. The values
`2^n − n − 1` are 0, 1, 4, 11, 26, 57, 120, 247, 502, 1013. The formula fails in every
degree `3 ≤ n ≤ 10` under both conventions.

Readings: the statement explicitly names *noncommutative* symmetric functions.
Commutative Sym and QSym have 1-dimensional primitive spaces, which would match only the
degenerate 1-based value `A(n,1) = 1`, but neither is the algebra in the conjecture.
Two other readings also give 1-dimensional pieces, matching only the 1-based value 1: the
Lie algebra of infinitesimal characters of NSym (`= Prim(QSym)`) and the indecomposables
`Q(NSym)`. Neither is the object the statement names. The clause "n-th homogeneous
dimension … verifiable for n ≤ 10" only makes sense for `Prim(Sym)` itself, so the graded
reading is the only one with checkable content. Other Eulerian-type numbers also differ
from 2 at `n = 3`: type B gives `B(3,1) ∈ {23, 1}`, and second-order gives `⟨⟨3,1⟩⟩ ∈ {8, 1}`.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only Python 3's standard library. It
  computes `dim Prim(NSym)_n` in three ways: as the coproduct kernel (exact over ℚ for
  `n ≤ 8`, mod a prime for `n ≤ 10`), by duality with QSym's quasi-shuffle product
  (`n ≤ 7`), and from the PBW identity `Π(1−t^k)^{−p_k} = (1−t)/(1−2t)` (`n ≤ 10`). It
  also computes Eulerian numbers by brute force (`n ≤ 9`) and by the closed formula
  (`n ≤ 10`).
- `verification.txt`: the build log, forbidden-token scan, axiom audit and Python output.

## Lean

- Objects are built from scratch:
  - Compositions are `List Nat`. `comps n` is checked to list `2^(n−1)` distinct
    compositions for `n ≤ 8`.
  - A basis tensor `S^J ⊗ S^K` is the pair `(J, K)`, and a tensor is a formal integer
    combination compared coefficientwise.
  - `deltaS I` computes `Δ S^I = Π Δ S_{i_j}` in the tensor-square algebra.
  - `IsPrimitive n x` means `Δx − x⊗1 − 1⊗x = 0` for `x = Σ_I x(I) S^I`.
  - `PrimDim n m` means the primitive space has dimension `m`: `m` independent
    primitives exist, and any `m+1` primitives are dependent.
- `isPrimitive_three_iff` proves the criterion `a+b+c = 0 ∧ b+c+3d = 0` for all `x`.
- `primDim_three : PrimDim 3 2` uses the witnesses `Ψ_3` and `[S_2,S_1]`. Any three
  primitives satisfy an explicit integer relation built from 2×2 minors.
- `primDim_three_unique` proves that `PrimDim 3 m → m = 2`.
- Eulerian numbers: `perms n` enumerates permutations. For `n ≤ 5` it has `n!` distinct
  entries, and for `n = 3` the list is checked to be complete. `eulerDes0`, `eulerDes1`,
  `eulerAsc0` and `eulerAsc1` count by descents or ascents, 0- or 1-based.
  `eulerian_three` gives `A(3,1) = 4, 1, 4, 1`.
- `DimClause A := ∀ n ≥ 1, PrimDim n (A n 1)`. `conjecture_00000000438_false` proves
  `¬ DimClause` for all four conventions.
- `conjecture_00000000438_false_degree3` adds that `dim Prim_3 = 2 ≠ A(m,1)` for every
  `m ≤ 6` and every convention.
- Not in Lean: `A(m,1) ≠ 2` for `m ≥ 7` (an elementary lemma in the report) and the
  dimensions for `n ≠ 3`. Neither is needed for the refutation. Coefficients in Lean are
  integers. A lemma in the report (`ℤ` to `ℚ`) shows why this computes the ℚ-dimension:
  - the kernel of an integer matrix has a ℚ-basis of integer vectors;
  - integer vectors are ℤ-independent iff they are ℚ-independent.

The project has no `sorry`, no `native_decide`, and no added axioms.
`#print axioms` shows at most `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称：非交换对称函数 Hopf 代数 **Sym**（NSym）的本原李代数的第 n 齐次分量维数等于欧拉数
`A(n,1)`（并称其同构于某个未定义的"广义 Lie n-代数"；分次同构保持维数，因此只需反驳维数公式）。
该公式在 `n = 3` 处不成立。NSym 是由 `S_1, S_2, …` 生成的自由结合代数，余乘法为
`Δ S_k = Σ_{i+j=k} S_i ⊗ S_j`。3 次分量的基为 `S_3, S_21, S_12, S_111`。计算得
`x = aS_3 + bS_21 + cS_12 + dS_111` 为本原元当且仅当 `a+b+c = 0` 且 `b+c+3d = 0`，
因此本原空间维数为 2，基为 `Ψ_3 = 3S_3 − S_21 − 2S_12 + S_111` 与 `[S_2,S_1] = S_21 − S_12`
（在任意域上均如此）。而 `A(3,1)` 在"恰有一个下降"约定下为 4，在 1 起始约定（OEIS A008292）下为 1，
都不等于 2（B 型欧拉数 `B(3,1) ∈ {23, 1}`、二阶欧拉数 `⟨⟨3,1⟩⟩ ∈ {8, 1}` 也都不等于 2）。事实上 `A(m,1)` 只取 `2^m − m − 1` 或 1，永远不等于 2，所以任何下标平移也无法挽救该公式。
n = 1..10 时本原维数为 1, 1, 2, 3, 6, 9, 18, 30, 56, 99，从 n = 3 起与两种约定下的 `A(n,1)` 都不相等。
"第 n 齐次维数（可验证 n ≤ 10）"只对 Prim(Sym) 本身有意义，所以分次解读是唯一可检验的解读。
其他给出 1 维分量的解读（NSym 的无穷小特征李代数 = Prim(QSym)，以及不可分解元空间 Q(NSym)，
还有交换对称函数）只与 1 起始约定下的 1 相符，但都不是题目所说的对象。
Lean 中系数取整数；报告中的引理说明这等价于 ℚ 上的维数：整数矩阵的核有一组由整数向量组成的 ℚ-基，
并且整数向量 ℤ-线性无关当且仅当 ℚ-线性无关。
Lean 项目（仅用核心库）从定义出发构造 3 次分量的余乘法，证明本原空间维数恰为 2，
用置换的下降/上升计数定义欧拉数，并证明维数子句的否定。
