# Conjecture 00000001457: disproof

Author: [GodBlf](https://github.com/GodBlf). Submitted October 8, 2026.

In dimension two the conjecture predicts Banach–Mazur distance `2 - 1 = 1`
between a triangle and the `l1` unit ball. The submission proves a lower bound
of `2` for the actual infimum, allowing every invertible real linear map and
independent translations of the middle and outer bodies.

An affine image of the cross-polytope is centrally symmetric. If it contains
the three triangle vertices, it contains their reflections in its center.
Three inequalities for those reflected vertices in the outer dilated triangle
force the dilation factor to be at least `2`. An explicit admissible factor `4`
establishes nonemptiness before taking the infimum. No exact upper bound is
needed. This disproves the stated formula at `n = 2`; it does not resolve a
modified higher-dimensional or asymptotic conjecture.

## Submission files

- `main.tex` and `report.pdf`: complete mathematical argument and distance convention.
- `lean/Main.lean`: actual triangle and diamond sets, affine images, exact
  outer-dilation equivalence, all admissible factors, and the real-infimum disproof.
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
axioms, or numerical optimization is used. The theorem audit reports only
the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Rebuild the PDF from the submission directory with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -jobname=report main.tex
pdflatex -interaction=nonstopmode -halt-on-error -jobname=report main.tex
```

The PDF was rendered and visually inspected.

## 中文摘要

取二维标准三角形与 `l1` 单位球。任何包含三角形的交叉多面体仿射像均中心对称，
因而包含三个顶点的中心反射。将这些反射点代入外层三角形的三个边界不等式，
即可推出膨胀因子至少为 `2`。Lean 证明允许独立平移、任意可逆线性变换，
并证明可行集合非空和真实下确界至少为 `2`，从而严格否定题目在 `n = 2` 时
声称的距离 `1`。附完整 LaTeX、PDF、依赖锁定文件及编译公理审计。
