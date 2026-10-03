# Conjecture 00000007680: author notes

The exact count of partition-congruence residues fails at a=2, m=1.

Witness: Every sequence has every residue valid modulo 1, while omega(1)=0; positive b=1 is admissible.

Formal bridge: All residues and all indices are quantified. The arbitrary sequence theorem applies directly to the actual partition function.

Scope boundary: Uses the written positive-modulus domain, which includes m=1. Both zero-inclusive and positive-only residue conventions fail.

The proof source is `main.tex`. Exact bilingual source and its pinned upstream
reference are in `SOURCE.md`. The self-contained Lean project is in `lean/`.
It requires Lean 4.19.0 and imports only `Std`; it needs no Mathlib or external
Lean dependency. The main result is
`Conjecture7680.conjecture7680_counterexample`.

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
