# Conjecture 00000007689: author notes

Equality to Delannoy numbers and the claimed diagonal asymptotic are incompatible.

Witness: D(2n,2n)>=13^n for every n, and the diagonal admits no eventual integer C*3^m upper bound.

Formal bridge: The complete recurrence, uniqueness, monotonicity, and all-index growth contradiction are formalized.

Scope boundary: Lean proves the necessary integer-bound contradiction. The explicit elementary implication from the ordinary real asymptotic to that bound is proved in the text.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture7689.conjecture7689_counterexample`.

From `lean/`, with the prescribed Lean version on PATH, reproduce:

```text
lake clean
lake build
lean Main.lean
```

All three commands were actually run successfully. Their exact commands,
working directories, exit codes, and proof/source SHA-256 hashes are preserved
in `RESULT.json`, and their outputs are in `build_0.log`, `build_1.log`, and
`build_2.log`. The project treats Lean warnings as errors. The final Lean
commands print the axioms of the relevant results. No admitted proofs,
native evaluation proof shortcut, or custom axiom is used.

This folder is an author package. Independent semantic review and PDF
preparation are coordinated separately; no network write is part of its
proof or reproduction commands.
