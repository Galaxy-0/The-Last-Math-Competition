# Counterexample to conjecture 00000003327

The standard Fine numbers are not log-concave: the positive consecutive
terms `F_2 = 1`, `F_3 = 2`, `F_4 = 6` satisfy `F_3^2 = 4 < 6 = F_2 F_4`.
This refutes the conjecture's explicit Fine-number log-concavity clause.

Fine numbers count Dyck paths with no hills (peaks at height one).
The report derives the small values by first-return decomposition and
lists every path involved. See the definition in the introduction of
[Barcucci et al. (2001)](https://www.mat.univie.ac.at/~slc/wpapers/s46rinaldi.pdf).
No assertion about a modified, normalized, or eventually log-concave
sequence is needed.

## Contents

- `report.tex`, `report.pdf`: complete mathematical report.
- `lean4/`: self-contained Lean 4.19.0 project, standard library only.
- `verify.py`: independent exhaustive verification using Python 3's standard library.
- `verification.txt`: local build, axiom audit, and Python verification output.

## Reproduce

With Lean 4.19.0 available through `elan` or the official release binaries:

```sh
cd lean4
lake build
lake env lean Main.lean
cd ..
python verify.py
tectonic report.tex
```

The PDF can also be rebuilt with two runs of
`pdflatex -interaction=nonstopmode -halt-on-error report.tex`.

The Lean project proves that its word enumeration is exhaustive and
duplicate-free, and that the scanner accepts exactly hill-free Dyck paths.
The count equalities and final contradiction use kernel-checked `decide`.
The final negation and numerical lemmas depend on no axioms. The general
enumeration and semantic helper theorems use only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`, as recorded individually
by `#print axioms`; there are no added axioms or proof omissions.
The Python script separately cross-checks enumeration against the Catalan
first-return recurrence for semilengths 0 through 7.

## 中文说明

题目声称 Fine 数列具有对数凹性。采用标准定义：`F_n` 是半长为 `n`、
没有高度为 1 的峰的 Dyck 路径数量。直接计数得到相邻三项 `1, 2, 6`，
所以 `2² < 1×6`，违反对数凹性。反例位于全部为正的部分，不依赖首项附近的零。
Lean 从路径定义验证计数，并证明全称命题的否定；Python 为独立复核。

Prepared locally with OpenAI Codex for `ziangni-sys` on 2026-10-04.
Submitted for independent review.
