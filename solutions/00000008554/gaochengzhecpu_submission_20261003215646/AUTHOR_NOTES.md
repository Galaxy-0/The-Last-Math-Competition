# Conjecture 00000008554: author notes

The crosscut homological-dimension assertion fails in B2.

Witness: Its atom/coatom crosscut complex is two isolated vertices: ordinary and reduced homological dimensions are both 0, while rank minus one is 1.

Formal bridge: All lattice subsets, maximal chains, crosscut subsets, simplices, and all homological degrees are covered; positive chain groups vanish, forcing their boundaries.

Scope boundary: Ordinary Euler characteristic is 2 and reduced Euler characteristic is 1=Mobius number. The dimension counterexample works in both conventions; no claim about another algebraic invariant called dimension is made.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture8554.conjecture8554_counterexample`.

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
