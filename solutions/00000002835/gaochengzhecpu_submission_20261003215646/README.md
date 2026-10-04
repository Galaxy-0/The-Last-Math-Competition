# Conjecture 00000002835: Disproof

The distinct rank-one matrices [[1,1],[1,1]] and [[1,-1],[-1,1]] agree on both diagonal observations. Their bipartite observation graph is itself a perfect matching and hence 1-regular, yet those observations do not determine a unique rank-one completion.

## Scope

This refutes the sufficiency direction of the stated criterion at n=2 and r=1. Because the observation graph itself is regular on all row and column vertices, the example works with either spanning or nonspanning subgraph conventions. The rational witnesses also give nonuniqueness over the real and complex fields. Earlier withdrawn PR #237 by orionsheep addressed the necessity direction with a different rectangular example; this submission addresses sufficiency with a square example.

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

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000002835.md

Upstream statement rechecked at `4509328ceb3b63c07d05bc4c42c4f12e8fa3c94f`; unchanged from the pinned source. AI-assisted submission by **gaochengzhecpu**.
