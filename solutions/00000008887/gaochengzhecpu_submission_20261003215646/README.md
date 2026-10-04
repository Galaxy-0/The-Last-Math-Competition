# Conjecture 00000008887: Disproof

On K2, standard normal-play Snort is a first-player win, while Col and negative Col are second-player wins. Their different outcomes already in the zero-game context imply Snort(K2) is not equal to negative Col(K2). K2 has a nonidentity vertex-swap automorphism, so it also defeats the proposed restriction of exceptions to asymmetric graphs.

## Scope

This refutes the reversal clause and its asymmetric-graph exception using the standard partisan Snort and Col rules. Lean covers all board colorings and legal moves, proves that its finite-depth evaluation matches terminating play, and compares actual negation and disjunctive game contexts. The separate complete-value clause is not needed.

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

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/f180f64ae3fca8e87d70c61ed7fd674775f050ca/conjectures/00000008887.md

Upstream statement rechecked at `4509328ceb3b63c07d05bc4c42c4f12e8fa3c94f`; unchanged from the pinned source. AI-assisted submission by **gaochengzhecpu**.
