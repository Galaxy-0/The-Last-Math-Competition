# Conjecture 00000001255: disproof

Author: [GodBlf](https://github.com/GodBlf). Submitted October 8, 2026.

On a one-site binary periodic ring, use the deterministic flip rule `F(s) = !s`.
Apply the prescribed output with probability `3/4`, and its opposite with
probability `1/4`. The resulting strictly positive Markov kernel is
`[[1/4, 3/4], [3/4, 1/4]]`. Its unique stationary law is `(1/2, 1/2)`, hence an
extreme stationary law. The deterministic automaton has no fixed points.
This disproves the conjecture's extreme-point clause and therefore the whole
conjunction. The report also discusses the interpretation using the probability
simplex on the stationary support. No attractor-dimension convention is needed.

## Submission files

- `main.tex` and `report.pdf`: complete mathematical argument.
- `lean/Main.lean`: the real-valued kernel, all stationary laws, the extreme-point
  predicate, and the formal negation of the fixed-point clause.
- `lean/Check.lean`: axiom audit of the main theorems.
- `lean/lean-toolchain`, `lean/lakefile.toml`, and `lean/lake-manifest.json`:
  pinned, reproducible Lean 4 / Mathlib project.
- `verification.txt`: successful build and axiom-audit output.

## Reproduce

Install the toolchain in `lean/lean-toolchain`, then run:

```sh
cd lean
lake exe cache get
lake build
lake env lean Check.lean
```

The build was performed with Lean `4.35.0-rc3` and Mathlib revision
`aaf410c71d42d5dc083c7735e47f56443afca3c0`, using the pinned dependency manifest.
An existing dependency cache was reused; each submission had its own project
configuration and build directory. No `sorry`, `native_decide`, additional
axioms, or sampling is used. The theorem audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms; `no_fixed_points` needs none.

Rebuild the PDF from the submission directory with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -jobname=report main.tex
pdflatex -interaction=nonstopmode -halt-on-error -jobname=report main.tex
```

The PDF was rendered and visually inspected.

## 中文摘要

单格周期环上的二元翻转规则没有不动点。加入概率 `1/4` 的输出翻转噪声后，
转移矩阵每个元素都为正，唯一平稳分布是 `(1/2, 1/2)`。平稳分布集合为单点，
该分布自然是极点，但不对应任何确定性不动点。因此原猜想的极点断言为假。
Lean 证明覆盖全部实数概率分布及极点定义，附完整 LaTeX、PDF 和编译审计。
