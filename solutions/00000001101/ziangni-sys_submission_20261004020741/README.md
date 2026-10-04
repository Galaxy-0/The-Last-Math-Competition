# Disproof of 00000001101

The reduced irreducible root system A1 has Weyl group `{e,s}`. Its KL polynomials are `P(e,e)=P(e,s)=P(s,s)=1` and `P(s,e)=0`. Every nonzero leading coefficient is 1 and has no prime factor, disproving the universal statement. The report derives the table from KL normalization and degree conditions and independently from the rank-one bar-invariant Hecke basis.

The Lean proof covers arbitrary bounded-support integer polynomial families satisfying the standard rank-one KL conditions. It proves uniqueness coefficientwise, derives every leading coefficient, explicitly excludes the zero polynomial, and proves the negation of the existential claim. This is stronger than checking a hardcoded table. No custom axioms, admitted proofs, or native evaluation tactics occur. Standard logical dependencies are `propext` and `Quot.sound`. General root-system/Hecke theory is explained mathematically in the report rather than imported into Lean.

## Reproduce

```text
cd lean
lake build
lake env lean Main.lean
cd ..
python verify.py
tectonic report.tex
```

Lean version: 4.19.0; Python script: standard library only; report compiler: Tectonic 0.17.0. `verification.txt` records results. Only this personal submission directory is changed.

中文：A1 根系的 Weyl 群只有 e、s 两个元素。三个非零 Kazhdan–Lusztig 多项式均为常数 1，因此首项系数没有奇素因子。零多项式没有非零首项，不能作为猜想所要求的例子。报告给出完整的反例和定义对应关系；Lean 对满足标准 KL 条件的秩一情形的任意多项式族证明该结论。
