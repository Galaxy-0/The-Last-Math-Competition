# Conjecture 00000000024: FALSE

**Submitter: [SucRunBug](https://github.com/SucRunBug).** AI-assisted mathematical work and formalization.

Four colors suffice for all prime distances on the real line.

The complete argument and its interpretation boundary, where applicable, are in `main.tex` and `main.pdf`. The formalization scope is described explicitly in the document.

## Reproduce

```sh
python3 reproduce.py
cd lean4
lake exe cache get
lake build
lake env lean Check.lean
```

Versions: Lean and Mathlib `v4.33.0`. `Check.lean` reports the actual transitive axiom dependencies of the main theorems. Standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) may appear; no custom axioms, `sorry`, or `native_decide` are used.

## Verification status

`lake build`, `lake env lean Check.lean`, and the independent Python checks passed. The LaTeX source compiled successfully with the native desktop compiler. See `verification.txt` for actual command output and the proof-source hash. The theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. This is local verification; competition acceptance remains subject to organizer review.

## Files

- `main.tex`: standalone LaTeX source of the proof.
- `main.pdf`: readable PDF of the same argument.
- `lean4/`: pinned, reproducible Lean project.
- `reproduce.py`: independent computational sanity checks, not a substitute for the general proof.
