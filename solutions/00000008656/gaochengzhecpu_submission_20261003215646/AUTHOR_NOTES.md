# Conjecture 00000008656: author notes

The unique minimum representative in a Whitehead automorphism orbit does not exist in general.

Witness: In F(a,b), a and a inverse are distinct reduced words of minimal length one in the same full automorphism orbit.

Formal bridge: All signed words are quotiented by free cancellation; the full free-group universal property and all-automorphism/all-representative minimality are proved.

Scope boundary: Refutes literal uniqueness of minima. The source supplies no quotient by signed basis permutations or additional canonical tie-breaking rule.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture8656.conjecture8656_counterexample`.

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
