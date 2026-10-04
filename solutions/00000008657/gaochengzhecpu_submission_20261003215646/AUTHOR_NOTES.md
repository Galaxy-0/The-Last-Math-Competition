# Conjecture 00000008657: author notes

There cannot be a finite complete list of parameter pairs for finite Burnside groups.

Witness: For every m>=2 the actual quotient B(m,2) is finite, yielding infinitely many parameter pairs (m,2).

Formal bridge: The quotient includes square relations for every word; the exponent-two universal property and coverage of all quotient elements by a length-2^m list are proved for every m.

Scope boundary: The finite-pair clause is read as written, with m variable and no odd-exponent restriction on this separate clause. The proof does not address finite descriptions by parameterized families.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture8657.conjecture8657_counterexample`.

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
