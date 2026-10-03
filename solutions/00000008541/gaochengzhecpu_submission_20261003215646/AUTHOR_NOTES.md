# Conjecture 00000008541: author notes

The asserted exponential growth for all free lattices fails at two generators.

Witness: The free unbounded lattice on two generators has four elements, so every family of balls is bounded by four.

Formal bridge: The lattice laws and universal existence-and-uniqueness property to every lattice are proved. Arbitrary predicate subsets and all ball families are covered.

Scope boundary: Uses the ordinary meet/join lattice signature and the source as written, with no n>=3 restriction. The bound does not depend on a specific word-length convention.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture8541.conjecture8541_counterexample`.

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
