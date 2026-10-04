# Conjecture 00000002353: Disproof

For the one-variable noncommutative rational function r(x)=x^(-1), the full matrix domain consists of invertible matrices. At size one, [1] and [-1] belong to the domain but their midpoint [0] does not, contradicting the fixed-size convexity required by matrix convexity.

## Scope

The witness works over the real and complex fields and uses self-adjoint matrices. It concerns the full matrix well-definedness domain named in the source, rather than a chosen positive-definite branch or positivity component. Failure of the matrix-convexity clause suffices to refute the stated conjunction.

## Contents and reproduction

- `main.tex` and `main.pdf`: full argument, stated scope, and formalization bridge.
- `lean/`: complete Lean 4.19.0 project using bundled Std only.
- `conjecture.md`: exact upstream bilingual statement; `SOURCE.md` and `AUTHOR_NOTES.md` preserve source and author notes.
- `verification/`: actual build logs, original author records, PDF checks, and independent review.
- `VALIDATION.json`: authoritative SHA-256 hashes for the files in this submission.

With Lean 4.19.0 installed, run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Compile `main.tex` with Tectonic or a standard LaTeX distribution. Any auxiliary Python source used in the argument is included in this directory. The Lean source, project configuration, LaTeX source, and PDF are byte-identical to the independently reviewed local release. The PDF was compiled and all pages were visually inspected.

Original author records describe earlier validation stages and may contain pre-layout manuscript hashes or earlier pending/publication statuses. Their historical fields are preserved; `VALIDATION.json` contains current file hashes. They do not supersede the final independent review or PDF validation.

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000002353.md

Upstream statement rechecked at `4509328ceb3b63c07d05bc4c42c4f12e8fa3c94f`; unchanged from the pinned source. AI-assisted submission by **gaochengzhecpu**.
