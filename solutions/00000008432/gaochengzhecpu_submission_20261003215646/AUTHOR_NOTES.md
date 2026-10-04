# Conjecture 00000008432: author notes

The rank=t+1 assertion for a minimum-support t-design fails.

Witness: The binary [7,3,4] simplex code has an exact-strength-2 support design 2-(7,4,2), of hypergraph rank 4.

Formal bridge: All binary words and predicate supports are represented; all minimum supports and all coordinate pairs are covered.

Scope boundary: Hypergraph rank means maximum edge cardinality, the standard definition. Exact strength 2 is checked, so t is not an arbitrarily weakened design parameter.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture8432.conjecture8432_counterexample`.

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
