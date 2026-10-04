# Disproof of conjecture 00000003943

The classical iterative augmenting-path matching algorithm uses at most `floor(n/2)` paths: toggling a simple augmenting path increases matching size by exactly one. This refutes the claimed `Theta(n^2 log n)` worst-case augmentation count. The report explicitly distinguishes the algorithm's selected augmenting paths from all candidate paths or failed search operations.

## Materials

- `conjecture.md`: exact original bilingual statement.
- `report.tex`, `report.pdf`: complete mathematical disproof, semantic scope, and formalization details.
- `lean/`: self-contained Lean 4.19.0 project importing only Std.
- `verify.py`: independent exhaustive graph/path checks and tight examples.
- `verification/`: actual build, axiom, Python, and PDF verification records.

## Reproduce

```text
cd lean
lake build
lake env lean Main.lean
cd ..
python verify.py
tectonic report.tex
```

The Lean proof contains actual graphs, matchings with vertex-disjoint endpoints, simple alternating paths, and their remove-and-insert toggle. It proves matching capacity, cardinality increase, a universal run bound, and negates the asymptotic lower law with `n^2 floor(log2 n)`, an equivalent growth scale. A run stores its valid intermediate matchings; the report proves that the path toggle preserves the matching invariant. The redundant no-repeated-removed-edges condition is automatic for any simple path.

All audited theorems depend only on Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms, admitted proofs, `sorry`, or `native_decide` are used. The exact tight worst case `floor(n/2)` is also proved in the report by disjoint-edge graphs; no exact worst-case maximization is needed for the Lean disproof.

## 中文摘要

经典增广路匹配算法每次沿简单增广路取对称差，匹配边数恰好增加一。n 个顶点的匹配至多含 floor(n/2) 条边，故任意运行使用的增广路总数不超过 floor(n/2)，与猜想所称的 Theta(n² log n) 矛盾。这里计数的是经典迭代算法实际选择并用于增广的路径；报告明确区分了全部候选路径和搜索内部操作等不同计数。提交含完整数学证明、Lean 4 项目、独立穷举验证及 PDF。
