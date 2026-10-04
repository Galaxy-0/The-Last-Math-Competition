# Conjecture 00000006551: Disproof

The consistent splitting exp(3hA/4) exp(hB) exp(hA/4) has leading error h^2[A,B]/4 relative to exp(h(A+B)). Explicit noncommuting 2-by-2 matrices make this term nonzero, so the method has exactly first order and its leading commutator coefficient is 1/4, rather than the asserted universal 1/2.

## Scope

The source states the claim for first-order fractional-step methods generally. This positive, three-stage example refutes that universal claim; it does not dispute the familiar coefficient 1/2 for the particular two-stage Lie-Trotter method. Reversing the error convention changes the sign but not the magnitude of the counterexample's coefficient.

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

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000006551.md

Upstream statement rechecked at `4509328ceb3b63c07d05bc4c42c4f12e8fa3c94f`; unchanged from the pinned source. AI-assisted submission by **gaochengzhecpu**.
