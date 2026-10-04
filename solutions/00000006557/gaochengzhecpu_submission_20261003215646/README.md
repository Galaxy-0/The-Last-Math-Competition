# Conjecture 00000006557: Disproof

Let S(t) = exp(tA/2) exp(tB) exp(tA/2). The palindromic composition S(h/6)^4 S(-h/3) S(h/6)^4 has order at least four. After merging adjacent stages of the same operator, its 19 nonzero stages have negative coefficients -1/12, -1/3, and -1/12. Their signed sum is -1/2 and their magnitude sum is 1/2, so neither reading gives the asserted value 1.

## Scope

The counterexample is normalized so that the coefficients for each operator sum to 1, and the proof verifies every noncommutative word through degree four for the actual splitting. It refutes only the additional numerical assertion about the sum of negative coefficients; it does not refute the usual necessity of some negative coefficients in higher-order real splittings.

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

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000006557.md

Upstream statement rechecked at `4509328ceb3b63c07d05bc4c42c4f12e8fa3c94f`; unchanged from the pinned source. AI-assisted submission by **gaochengzhecpu**.
